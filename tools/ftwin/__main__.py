"""ftwin command line: run both sides of a twin lab and print one comparison."""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Dict, List, Optional

import tomllib

REPO = Path(__file__).resolve().parents[2]


@dataclass
class Result:
    """One verdict, normalised across both sides (ARCHITECTURE §4.3)."""
    design: str
    side: str                       # "mc" | "lean"
    engine: str
    property: str
    status: str                     # mc: proven | cex | bounded | covered | unreached | error
                                    # lean: proved | sorry | missing | error
    depth: Optional[int] = None
    time_s: float = 0.0
    cex_vcd: Optional[str] = None
    axioms: List[str] = field(default_factory=list)
    task: Optional[str] = None
    note: str = ""


# ------------------------------------------------------------------ SBY side
def _sby_cmd() -> List[str]:
    if shutil.which("sby"):
        return ["sby"]
    if shutil.which("yowasp-sby"):
        return ["yowasp-sby", "--yosys", "yowasp-yosys", "--smtbmc", "yowasp-yosys-smtbmc",
                "--witness", "yowasp-yosys-witness"]
    raise RuntimeError("SymbiYosys not found (install the OSS CAD Suite or `pip install yowasp-yosys`)")


def _sby_options(sby_text: str, task: str) -> Dict[str, str]:
    opts: Dict[str, str] = {}
    section = None
    for raw in sby_text.splitlines():
        line = raw.split("#", 1)[0].strip()
        if line.startswith("["):
            section = line.strip("[]")
            continue
        if section != "options" or not line:
            continue
        if ":" in line.split()[0]:
            t, rest = line.split(":", 1)
            if t.strip() != task:
                continue
            line = rest.strip()
        k, *v = line.split()
        opts[k] = " ".join(v)
    return opts


def run_sby(design: str, ddir: Path, cfg: dict, asserts: List[str], workdir: Path) -> List[Result]:
    sby_file = cfg["sby"]["file"]
    sby_text = (ddir / sby_file).read_text()
    out: List[Result] = []
    for task in cfg["sby"]["tasks"]:
        opts = _sby_options(sby_text, task)
        mode = opts.get("mode", "bmc")
        depth = int(opts["depth"]) if "depth" in opts else None
        shutil.copy(ddir / sby_file, workdir / sby_file)
        for f in cfg["files"]:
            shutil.copy(ddir / f, workdir / f)
        t0 = time.perf_counter()
        p = subprocess.run(_sby_cmd() + ["-f", sby_file, task], cwd=workdir,
                           capture_output=True, text=True)
        dt = round(time.perf_counter() - t0, 2)
        log = p.stdout + p.stderr
        engine = (re.search(r"engine_0: (.+?)$", log, re.M) or [None, "?"])[1].strip()
        if engine.startswith("starting process"):
            engine = "?"
        m_eng = re.search(r"summary: engine_0 \((.+?)\)", log)
        if m_eng:
            engine = m_eng.group(1)
        done = re.search(r"DONE \((\w+), rc=(\d+)\)", log)
        verdict = done.group(1) if done else "ERROR"
        failed = re.findall(r"(?<!induction): +## +\S+ +Assert failed in \S+: (\S+)", log)
        # a failing induction step is not a counterexample: the base case passed, so the
        # verdict is UNKNOWN (Jasper: "undetermined"); the trace starts in an arbitrary state
        induct = re.findall(r"induction: +## +\S+ +Assert failed in \S+: (\S+)", log)
        steps = [int(s) for s in re.findall(r"Checking assertions in step (\d+)", log)]
        fail_step = steps[-1] if (failed and steps) else None
        reached = re.findall(r"Reached cover statement in step (\d+) at \S+: (\S+)", log)
        vcd = workdir / f"{Path(sby_file).stem}_{task}" / "engine_0" / "trace.vcd"
        if mode == "cover":
            for step, label in reached:
                out.append(Result(design, "mc", engine, label, "covered", int(step), dt, task=task))
            continue
        for label in asserts:
            if verdict == "UNKNOWN" and label in induct and label not in failed:
                ivcd = workdir / f"{Path(sby_file).stem}_{task}" / "engine_0" / "trace_induct.vcd"
                out.append(Result(design, "mc", engine, label, "inconclusive", depth, dt,
                                  str(ivcd) if ivcd.exists() else None, task=task,
                                  note=f"induction step fails at k={depth}; base case passed"))
            elif verdict == "UNKNOWN" and induct:
                out.append(Result(design, "mc", engine, label, "unchecked", depth, dt, task=task,
                                  note="induction stopped at the first failing assertion"))
            elif label in failed:
                out.append(Result(design, "mc", engine, label, "cex", fail_step, dt,
                                  str(vcd) if vcd.exists() else None, task=task,
                                  note="expected" if task == "bug" else ""))
            elif verdict in ("PASS", "FAIL") and not failed:
                status = "proven" if mode == "prove" else "bounded"
                out.append(Result(design, "mc", engine, label, status, depth, dt, task=task))
            elif verdict == "FAIL":
                out.append(Result(design, "mc", engine, label, "unchecked", fail_step, dt, task=task,
                                  note="BMC stopped at the first failing assertion"))
            else:
                out.append(Result(design, "mc", engine, label, "error", depth, dt, task=task,
                                  note=log[-300:]))
    return out


# ----------------------------------------------------------------- Lean side
def run_lean(design: str, cfg: dict, asserts: List[str]) -> List[Result]:
    lean = cfg["lean"]
    lake = os.environ.get("LAKE") or shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
    t0 = time.perf_counter()
    b = subprocess.run([lake, "build", lean["module"]], cwd=REPO, capture_output=True, text=True)
    build_s = round(time.perf_counter() - t0, 2)
    out: List[Result] = []
    if b.returncode != 0:
        return [Result(design, "lean", "lean", a, "error", note=(b.stdout + b.stderr)[-400:])
                for a in asserts]
    thms = lean.get("theorems", {})
    out = check_theorems(design, f"import {lean['module']}\n", thms, asserts, lake)
    for r in out:
        if r.status in ("proved", "sorry"):
            r.time_s = build_s
    return out


def check_theorems(design: str, source: str, thms: Dict[str, str], asserts: List[str],
                   lake: Optional[str] = None) -> List[Result]:
    """Compile `source` followed by `#print axioms` for each theorem; one Result per assert."""
    lake = lake or os.environ.get("LAKE") or shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
    probe = [source.rstrip("\n")] + [f"#print axioms {thms[a]}" for a in asserts if a in thms]
    (REPO / "build").mkdir(exist_ok=True)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=REPO / "build", delete=False) as f:
        f.write("\n".join(probe) + "\n")
        path = f.name
    t0 = time.perf_counter()
    try:
        p = subprocess.run([lake, "env", "lean", path], cwd=REPO, capture_output=True, text=True)
    finally:
        os.unlink(path)
    dt = round(time.perf_counter() - t0, 2)
    text = p.stdout + p.stderr
    errors = [l for l in text.splitlines() if ": error" in l]
    out: List[Result] = []
    for a in asserts:
        if a not in thms:
            out.append(Result(design, "lean", "lean", a, "missing", note="no theorem in twin.toml"))
            continue
        name = thms[a]
        m = re.search(rf"'{re.escape(name)}' depends on axioms: \[([^\]]*)\]", text, re.S)
        if m:
            axioms = [x.strip() for x in m.group(1).replace("\n", " ").split(",") if x.strip()]
        elif f"'{name}' does not depend on any axioms" in text:
            axioms = []
        else:
            out.append(Result(design, "lean", "lean", a, "error", time_s=dt,
                              note=(errors[0] if errors else text[-300:])[:400]))
            continue
        if "sorryAx" in axioms and errors:
            # Lean replaces a proof that fails with `sorry` so it can keep going
            out.append(Result(design, "lean", "lean", a, "failed", time_s=dt, axioms=axioms,
                              note=f"{name}: {errors[0][:300]}"))
            continue
        status = "sorry" if "sorryAx" in axioms else "proved"
        out.append(Result(design, "lean", "lean (kernel-checked)", a, status, time_s=dt,
                          axioms=axioms, note=name))
    return out


# ------------------------------------------------------------------- report
def _short_axioms(ax: List[str]) -> str:
    std = {"propext", "Classical.choice", "Quot.sound"}
    extra = [("bv_decide (native)" if "._native.bv_decide" in a else
              "native_decide" if "._native." in a else a) for a in ax if a not in std]
    return "kernel" + (" + " + ", ".join(sorted(set(extra))) if extra else "")


def report(results: List[Result]) -> str:
    rows = [("property", "side", "task/engine", "verdict", "depth", "time", "trusts / evidence")]
    for r in sorted(results, key=lambda r: (r.property, r.side != "mc", r.task or "")):
        if r.side == "mc":
            ev = r.cex_vcd and Path(r.cex_vcd).name or ""
            ev = (f"CEX {ev}" if r.status == "cex" else ev) + (f" ({r.note})" if r.note and r.status == "cex" else "")
            rows.append((r.property, "MC", f"{r.task}: {r.engine}", r.status,
                         "" if r.depth is None else str(r.depth), f"{r.time_s}s", ev or "engine"))
        else:
            rows.append((r.property, "Lean", r.note or r.engine, r.status, "∞" if r.status == "proved" else "",
                         f"{r.time_s}s", _short_axioms(r.axioms) if r.status == "proved" else r.note[:60]))
    widths = [max(len(row[i]) for row in rows) for i in range(len(rows[0]))]
    lines = ["  ".join(c.ljust(w) for c, w in zip(row, widths)) for row in rows]
    lines.insert(1, "  ".join("-" * w for w in widths))
    return "\n".join(lines)


def cmd_run(a: argparse.Namespace) -> int:
    ddir = REPO / "rtl" / a.design
    cfg = tomllib.loads((ddir / "twin.toml").read_text())
    asserts = sorted(cfg["lean"].get("theorems", {}).keys())
    results: List[Result] = []
    if not a.lean_only:
        work = REPO / "build" / "ftwin" / a.design
        work.mkdir(parents=True, exist_ok=True)
        results += run_sby(a.design, ddir, cfg, asserts, work)
    if not a.mc_only:
        results += run_lean(a.design, cfg, asserts)
    print(report(results))
    if a.json:
        Path(a.json).parent.mkdir(parents=True, exist_ok=True)
        Path(a.json).write_text(json.dumps([asdict(r) for r in results], indent=2))
    bad = [r for r in results if r.status in ("error", "failed") or (r.status == "cex" and r.note != "expected")]
    return 1 if bad else 0


def cmd_bench(a: argparse.Namespace) -> int:
    """Sweep one parameter: a BMC run per value, next to one all-values Lean theorem."""
    ddir = REPO / "rtl" / a.design
    cfg = tomllib.loads((ddir / "twin.toml").read_text())
    b = cfg["bench"]
    values = [int(v) for v in a.values.split(",")] if a.values else b["values"]
    work = REPO / "build" / "ftwin" / f"{a.design}_bench"
    work.mkdir(parents=True, exist_ok=True)
    for f in cfg["files"]:
        shutil.copy(ddir / f, work / f)
    rows = []
    for v in values:
        reads = "\n".join(f"read -formal {f}" for f in cfg["files"])
        (work / "bench.sby").write_text(
            f"[options]\nmode {b.get('mode', 'bmc')}\ndepth {b.get('depth', 1)}\n[engines]\n{b['engine']}\n"
            f"[script]\n{reads}\nchparam -set {b['param']} {v} {cfg['top']}\nprep -top {cfg['top']}\n"
            f"[files]\n" + "\n".join(cfg["files"]) + "\n")
        t0 = time.perf_counter()
        try:
            p = subprocess.run(_sby_cmd() + ["-f", "bench.sby"], cwd=work, capture_output=True,
                               text=True, timeout=a.timeout)
            done = re.search(r"DONE \((\w+), rc=", p.stdout + p.stderr)
            status = done.group(1) if done else "ERROR"
        except subprocess.TimeoutExpired:
            status = "TIMEOUT"
        dt = round(time.perf_counter() - t0, 2)
        rows.append({"param": b["param"], "value": v, "engine": b["engine"], "status": status, "time_s": dt})
        print(f"{b['param']}={v:<4} {b['engine']:<12} {status:<8} {dt:>8.2f}s", flush=True)
    thm = b.get("all_values_theorem")
    if thm:
        lake = os.environ.get("LAKE") or shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
        mod = cfg["lean"]["module"]
        subprocess.run([lake, "build", mod], cwd=REPO, capture_output=True)
        (REPO / "build").mkdir(exist_ok=True)
        probe = REPO / "build" / "ftwin_bench_probe.lean"
        probe.write_text(f"import {mod}\n#print axioms {thm}\n")
        t0 = time.perf_counter()
        p = subprocess.run([lake, "env", "lean", str(probe)], cwd=REPO, capture_output=True, text=True)
        dt = round(time.perf_counter() - t0, 2)
        ok = "depends on axioms" in p.stdout and "sorryAx" not in p.stdout
        print(f"{b['param']}=all  Lean         {'PROVED' if ok else 'ERROR':<8} {dt:>8.2f}s   {thm} "
              f"(one proof, every {b['param']}; time = load + check)")
        rows.append({"param": b["param"], "value": "all", "engine": "lean", "status": "PROVED" if ok else "ERROR",
                     "time_s": dt, "theorem": thm})
    if a.csv:
        Path(a.csv).parent.mkdir(parents=True, exist_ok=True)
        with open(a.csv, "w") as f:
            f.write("param,value,engine,status,time_s\n")
            for r in rows:
                f.write(f"{r['param']},{r['value']},{r['engine']},{r['status']},{r['time_s']}\n")
    return 0


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(prog="ftwin", description=__doc__)
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run", help="run both sides for rtl/<design>")
    r.add_argument("design")
    r.add_argument("--json")
    r.add_argument("--mc-only", action="store_true")
    r.add_argument("--lean-only", action="store_true")
    r.set_defaults(fn=cmd_run)
    b = sub.add_parser("bench", help="sweep a parameter: BMC time per value vs one Lean theorem")
    b.add_argument("design")
    b.add_argument("--values", help="comma-separated, overrides twin.toml")
    b.add_argument("--timeout", type=float, default=300)
    b.add_argument("--csv")
    b.set_defaults(fn=cmd_bench)
    sub.add_parser("tutor", help="ask the AI tutor (same as the `tutor` command)", add_help=False)
    argv = sys.argv[1:] if argv is None else argv
    if argv and argv[0] == "tutor":
        from tutor.__main__ import main as tutor_main
        return tutor_main(argv[1:])
    a = ap.parse_args(argv)
    return a.fn(a)


if __name__ == "__main__":
    sys.exit(main())
