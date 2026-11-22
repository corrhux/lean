"""Proof vs. Search web app: a local, offline API over the course tools (SPEC §6.7).

    pip install -e ".[app]"
    pvs-app                      # http://127.0.0.1:8000  (localhost only by default)

Every endpoint wraps an existing command-line tool, so the app and the CLI
always agree: `ftwin run`, `satlab gen`/`zoo`, the tutor's `check_lean`,
`read_file` and `cex_summary`.
"""

from __future__ import annotations

import json
from contextlib import asynccontextmanager
import os
import re
import shutil
import subprocess
import sys
import tomllib
from pathlib import Path
from typing import Dict, List, Optional

from fastapi import FastAPI, HTTPException
from fastapi.responses import FileResponse, PlainTextResponse, StreamingResponse
from fastapi.staticfiles import StaticFiles
from pydantic import BaseModel, Field

REPO = Path(__file__).resolve().parents[2]
STATIC = Path(__file__).resolve().parents[1] / "frontend"
RESULTS = REPO / "build" / "app"

sys.path.insert(0, str(REPO / "tools"))
from tutor import tools as ttools  # noqa: E402

sys.path.insert(0, str(Path(__file__).resolve().parent))
import workspace  # noqa: E402
from lean_lsp import LeanServer  # noqa: E402

LEAN = LeanServer()
PREFIX: Dict[str, int] = {}          # live-document key -> lines before the editor's text


@asynccontextmanager
async def lifespan(_app):
    yield
    LEAN.close()                     # stop the Lean server with the app


app = FastAPI(title="Proof vs. Search", docs_url="/api/docs", lifespan=lifespan)


def _designs() -> Dict[str, dict]:
    out = {}
    for toml in sorted((REPO / "rtl").glob("*/twin.toml")):
        cfg = tomllib.loads(toml.read_text())
        name = toml.parent.name
        lean = cfg.get("lean", {})
        module = lean.get("module", "")
        sol = "RtlProof/" + "/".join(module.split(".")[1:]) + ".lean" if module else None
        ex = sol.replace("Solution.lean", "Exercise.lean") if sol else None
        out[name] = {
            "name": name,
            "top": cfg.get("top"),
            "rtl": [f"rtl/{name}/{f}" for f in cfg.get("files", [])],
            "readme": f"rtl/{name}/README.md",
            "sby": f"rtl/{name}/{cfg['sby']['file']}" if "sby" in cfg else None,
            "sby_tasks": cfg.get("sby", {}).get("tasks", []),
            "generated": lean.get("generated"),
            "solution": sol if sol and (REPO / sol).exists() else None,
            "exercise": ex if ex and (REPO / ex).exists() else None,
            "theorems": lean.get("theorems", {}),
            "bench": cfg.get("bench"),
        }
    return out


COURSE_ORDER = ["counter", "mul", "fifo", "arbiter"]


@app.get("/api/designs")
def designs() -> List[dict]:
    """Twin-lab designs, in course order (then any others alphabetically)."""
    rank = {n: i for i, n in enumerate(COURSE_ORDER)}
    return sorted(_designs().values(), key=lambda d: (rank.get(d["name"], len(rank)), d["name"]))


@app.get("/api/designs/{name}/last")
def last_result(name: str) -> List[dict]:
    path = RESULTS / f"{name}.json"
    if name not in _designs() or not path.exists():
        raise HTTPException(404, "no saved run for this design yet")
    return json.loads(path.read_text())


class RunRequest(BaseModel):
    rtl: Dict[str, str] = {}            # file name -> edited text (unchanged files may be omitted)
    solution: Optional[str] = Field(None, max_length=400_000)


@app.post("/api/designs/{name}/run")
def run_design(name: str, req: Optional[RunRequest] = None) -> List[dict]:
    """Run both sides (`ftwin run`): every SymbiYosys task and every Lean theorem, on the
    committed design or, with edits, on a workspace copy (`workspace.py`)."""
    if name not in _designs():
        raise HTTPException(404, f"unknown design {name!r}")
    RESULTS.mkdir(parents=True, exist_ok=True)
    out = RESULTS / f"{name}.json"
    if req and (req.rtl or req.solution is not None):
        try:
            rows = workspace.run(name, req.rtl, req.solution)
        except workspace.WorkspaceError as e:
            raise HTTPException(400, str(e))
        out.write_text(json.dumps(rows, indent=2))
        return rows
    p = subprocess.run([sys.executable, "-m", "ftwin", "run", name, "--json", str(out)], cwd=REPO,
                       capture_output=True, text=True, timeout=1800,
                       env={**os.environ, "PYTHONPATH": str(REPO / "tools")})
    if not out.exists():
        raise HTTPException(500, (p.stdout + p.stderr)[-2000:])
    rows = json.loads(out.read_text())
    for r in rows:                                    # paths relative to the repo, for /api/file
        if r.get("cex_vcd"):
            r["cex_vcd"] = str(Path(r["cex_vcd"]).resolve().relative_to(REPO))
    out.write_text(json.dumps(rows, indent=2))
    return rows


@app.get("/api/designs/{name}/workspace")
def design_workspace(name: str) -> dict:
    """The committed texts the twin editors start from."""
    if name not in _designs():
        raise HTTPException(404, f"unknown design {name!r}")
    cfg = workspace.config(name)
    sol = workspace.solution_path(cfg)
    return {"rtl": {f: (REPO / "rtl" / name / f).read_text() for f in cfg["files"]},
            "solution_path": str(sol.relative_to(REPO)), "solution": sol.read_text()}


class BenchRequest(BaseModel):
    values: Optional[List[int]] = Field(None, max_length=12)
    timeout: float = Field(60, gt=0, le=600)


@app.post("/api/designs/{name}/bench")
def bench(name: str, req: BenchRequest) -> dict:
    """`ftwin bench`: one model-checking run per parameter value, next to one Lean theorem."""
    d = _designs().get(name)
    if not d or not d.get("bench"):
        raise HTTPException(404, f"no benchmark for {name!r}")
    RESULTS.mkdir(parents=True, exist_ok=True)
    csv = RESULTS / f"{name}.bench.csv"
    cmd = [sys.executable, "-m", "ftwin", "bench", name, "--csv", str(csv), "--timeout", str(req.timeout)]
    if req.values:
        cmd += ["--values", ",".join(str(v) for v in req.values)]
    p = subprocess.run(cmd, cwd=REPO, capture_output=True, text=True, timeout=3600,
                       env={**os.environ, "PYTHONPATH": str(REPO / "tools")})
    if not csv.exists():
        raise HTTPException(500, (p.stdout + p.stderr)[-2000:])
    result = {"bench": d["bench"], "rows": _read_bench(csv)}
    (RESULTS / f"{name}.bench.json").write_text(json.dumps(result, indent=2))
    return result


@app.get("/api/designs/{name}/bench/last")
def bench_last(name: str) -> dict:
    p = RESULTS / f"{name}.bench.json"
    if name not in _designs() or not p.exists():
        raise HTTPException(404, "no saved benchmark for this design yet")
    return json.loads(p.read_text())


def _read_bench(csv: Path) -> List[dict]:
    lines = csv.read_text().strip().splitlines()
    keys = lines[0].split(",")
    rows = []
    for line in lines[1:]:
        r = dict(zip(keys, line.split(",")))
        r["time_s"] = float(r["time_s"])
        rows.append(r)
    return rows


@app.get("/api/file", response_class=PlainTextResponse)
def read_file(path: str) -> str:
    text = ttools.read_file(path)
    if text.startswith(("Refused:", "No such file")):
        raise HTTPException(404, text)
    return text


@app.get("/api/cex", response_class=PlainTextResponse)
def cex(path: str) -> str:
    if not path.endswith(".vcd"):
        raise HTTPException(400, "expected a .vcd file")
    return ttools.cex_summary(path)


@app.get("/api/vcd")
def vcd(path: str) -> dict:
    """A counterexample trace as one value per clock step for each signal (for the waveform view)."""
    p = (REPO / path).resolve()
    if not path.endswith(".vcd") or REPO not in p.parents or not p.is_file():
        raise HTTPException(404, f"no VCD at {path}")
    sigs, changes = ttools.parse_vcd(p.read_text())
    times = sorted({t for t, _ in changes})
    steps = changes[::2] if len(times) > 2 else changes     # one sample per clock period
    out = []
    for ident, (name, width) in sigs.items():
        short = name.split(".")[-1]
        if short.startswith(("$", "_")):
            continue
        out.append({"name": name, "short": short, "width": width,
                    "values": [vals.get(ident) for _, vals in steps]})
    out.sort(key=lambda s: (s["short"] in ("clk", "clock"), s["name"]))
    return {"steps": len(steps), "signals": out}


KEY = r"^[A-Za-z0-9_-]{1,40}$"


class LeanSync(BaseModel):
    key: str = Field(pattern=KEY)
    code: str = Field(max_length=400_000)
    design: Optional[str] = None          # twin workspace: check against this design's model
    rtl: Dict[str, str] = {}              # ... regenerated from these RTL edits


@app.post("/api/lean/sync")
def lean_sync(req: LeanSync) -> dict:
    """Live editor: elaborate the document in a persistent Lean server; return diagnostics."""
    prefix, regenerated, text = 0, False, req.code
    if req.design:
        if req.design not in _designs():
            raise HTTPException(404, f"unknown design {req.design!r}")
        try:
            doc = workspace.assemble(req.design, req.code, req.rtl)
        except workspace.WorkspaceError as e:
            raise HTTPException(400, str(e))
        prefix, regenerated, text = doc.prefix_lines, doc.regenerated, doc.text
    try:
        r = LEAN.sync(req.key, text)
    except (TimeoutError, RuntimeError) as e:
        raise HTTPException(503, str(e))
    PREFIX[req.key] = prefix
    mine, model = [], []
    for d in r["diagnostics"]:
        if d["line"] >= prefix:
            mine.append({**d, "line": d["line"] - prefix, "endLine": d["endLine"] - prefix})
        else:
            model.append(d)
    return {"diagnostics": mine, "model_diagnostics": model, "regenerated": regenerated,
            "seconds": r["seconds"]}


class LeanGoal(BaseModel):
    key: str = Field(pattern=KEY)
    line: int = Field(ge=0)
    character: int = Field(ge=0)


@app.post("/api/lean/goal")
def lean_goal(req: LeanGoal) -> dict:
    """Tactic state and expected type at the cursor (what the VS Code infoview shows)."""
    try:
        return LEAN.goal(req.key, req.line + PREFIX.get(req.key, 0), req.character)
    except (TimeoutError, RuntimeError) as e:
        raise HTTPException(503, str(e))


class LeanCheck(BaseModel):
    code: str = Field(max_length=200_000)


@app.post("/api/lean/check")
def lean_check(req: LeanCheck) -> dict:
    """Compile a snippet in the project (the tutor's `check_lean`)."""
    return ttools.check_lean(req.code)


DOCS = ["course/README.md", "docs/LEAN_FLUENCY.md", "docs/COURSE.md", "docs/CAPSTONE_PRIMER.md",
        "docs/CAPSTONE_IBEX.md", "capstone/ibex/README.md", "docs/CAPSTONE_EXAM_PREP.md", "capstone/exam/README.md", "satlab/README.md", "docs/SPEC.md",
        "docs/ARCHITECTURE.md", "docs/REFERENCES.md", "README.md"]


@app.get("/api/docs-list")
def docs_list() -> List[dict]:
    out = []
    for d in DOCS:
        p = REPO / d
        if p.exists():
            title = next((l.lstrip("# ").strip() for l in p.read_text().splitlines() if l.startswith("# ")), d)
            out.append({"path": d, "title": title})
    return out


class ZooRequest(BaseModel):
    kind: str = Field(pattern=r"^(mul-miter|add-miter|pigeonhole|counter-bmc|random)$")
    width: int = Field(8, ge=1, le=16)
    n: int = Field(5, ge=1, le=12)
    timeout: float = Field(10, gt=0, le=120)
    solvers: List[str] = ["minisat22", "glucose4", "cadical195", "kissat404", "teach-cdcl"]


@app.post("/api/satlab/zoo")
def satlab_zoo(req: ZooRequest) -> dict:
    """Generate an instance and run it through several solvers (`satlab gen` + `satlab zoo`)."""
    from satlab import gen, zoo
    cnf = {"mul-miter": lambda: gen.mul_comm_miter(req.width),
           "add-miter": lambda: gen.add_comm_miter(req.width),
           "pigeonhole": lambda: gen.pigeonhole(req.n),
           "counter-bmc": lambda: gen.counter_bmc(12, wrap=10).cnf,
           "random": lambda: gen.random_ksat(10 * req.n, 43 * req.n, 3, 0)}[req.kind]()
    allowed = set(zoo.LINEAGE)
    solvers = [s for s in req.solvers if s in allowed]
    rows = zoo.run(cnf, solvers, req.timeout)
    for r in rows:
        r["about"] = zoo.LINEAGE.get(str(r["solver"]), "")
    return {"vars": cnf.num_vars, "clauses": len(cnf.clauses), "rows": rows}


# satlab's five labs (satlab/README.md), as fixed command lists: the app never runs other commands.
SAT_LABS = {
    1: ("Watch CDCL learn (B2)", [
        ["gen", "pigeonhole", "-n", "2", "-o", "php2.cnf"],
        ["solve", "php2.cnf", "--trace", "php2.jsonl"],
        ["trace", "php2.jsonl", "--names", "php2.cnf"]]),
    2: ("A counterexample from a SAT model (B4)", [
        ["gen", "counter-bmc", "--depth", "12", "--wrap", "10", "-o", "bug.cnf"],
        ["solve", "bug.cnf", "--model"]]),
    3: ("Why multipliers are hard for SAT (B3, D6)", [
        ["gen", "mul-miter", "--width", "4", "-o", "m4.cnf"], ["solve", "m4.cnf"],
        ["gen", "mul-miter", "--width", "6", "-o", "m6.cnf"], ["solve", "m6.cnf"],
        ["gen", "mul-miter", "--width", "8", "-o", "m8.cnf"], ["zoo", "m8.cnf", "--timeout", "20"]]),
    4: ("No heuristic wins everywhere (B3)", [
        ["gen", "mul-miter", "--width", "6", "-o", "m6.cnf"], ["ablate", "m6.cnf"],
        ["gen", "random", "-n", "150", "-m", "640", "--seed", "1", "-o", "r1.cnf"], ["ablate", "r1.cnf"]]),
    5: ("Checking an UNSAT answer (B5)", [
        ["gen", "mul-miter", "--width", "4", "-o", "m4.cnf"],
        ["solve", "m4.cnf", "--proof", "m4.drup"], ["check", "m4.cnf", "m4.drup"]]),
}


@app.get("/api/satlab/labs")
def satlab_labs() -> List[dict]:
    return [{"lab": k, "title": v[0], "commands": ["satlab " + " ".join(c) for c in v[1]]}
            for k, v in SAT_LABS.items()]


class LabRequest(BaseModel):
    lab: int = Field(ge=1, le=5)


@app.post("/api/satlab/lab")
def satlab_lab(req: LabRequest) -> dict:
    """Run one of satlab's labs, command by command, in `build/app/satlab/`."""
    import time
    work = RESULTS / "satlab"
    work.mkdir(parents=True, exist_ok=True)
    steps = []
    for cmd in SAT_LABS[req.lab][1]:
        t0 = time.perf_counter()
        try:
            p = subprocess.run([sys.executable, "-m", "satlab.cli", *cmd], cwd=work, capture_output=True,
                               text=True, timeout=300, env={**os.environ, "PYTHONPATH": str(REPO)})
            out = (p.stdout + p.stderr).strip()
        except subprocess.TimeoutExpired:
            out = "(stopped after 300 s)"
        steps.append({"command": "satlab " + " ".join(cmd), "output": out[-20000:],
                      "seconds": round(time.perf_counter() - t0, 2)})
    return {"lab": req.lab, "title": SAT_LABS[req.lab][0], "steps": steps}


class TutorRequest(BaseModel):
    question: str = Field(max_length=10_000)
    file: Optional[str] = None
    level: int = Field(2, ge=1, le=5)
    context: Optional[str] = Field(None, max_length=80_000)   # live editor state from the page


def _have_key() -> bool:
    return bool(os.environ.get("ANTHROPIC_API_KEY") or os.environ.get("ANTHROPIC_AUTH_TOKEN"))


_TUTOR = None


def tutor_client():
    """One tutor per app (single user), so follow-up questions keep the conversation."""
    global _TUTOR
    if _TUTOR is None:
        from tutor.client import Tutor
        _TUTOR = Tutor()
    return _TUTOR


@app.post("/api/tutor")
def tutor(req: TutorRequest) -> dict:
    if not _have_key():
        raise HTTPException(503, "The tutor needs ANTHROPIC_API_KEY. Everything else works without it.")
    from tutor.prompts import user_message
    turn = tutor_client().ask(user_message(req.question, req.level, req.file, context=req.context))
    return {"text": turn.text, "tools": turn.tool_calls, "model": turn.served_by}


@app.post("/api/tutor/stream")
def tutor_stream(req: TutorRequest) -> StreamingResponse:
    """The tutor's answer as server-sent events (`data: {json}`), text as it is written."""
    if not _have_key():
        raise HTTPException(503, "The tutor needs ANTHROPIC_API_KEY. Everything else works without it.")
    from tutor.client import explain_api_error
    from tutor.prompts import user_message
    msg = user_message(req.question, req.level, req.file, context=req.context)

    def events():
        try:
            for ev in tutor_client().stream(msg):
                yield f"data: {json.dumps(ev)}\n\n"
        except Exception as e:                       # report, don't drop the connection silently
            yield f"data: {json.dumps({'type': 'error', 'message': explain_api_error(e)})}\n\n"

    return StreamingResponse(events(), media_type="text/event-stream",
                             headers={"Cache-Control": "no-cache"})


# ------------------------------------------------------------------------ workbook
def _workbook() -> List[dict]:
    """The Lean files you work in: the lab exercises and the exam."""
    out = []
    for f in sorted((REPO / "RtlProof" / "Examples").glob("*/Exercise.lean")):
        out.append({"path": str(f.relative_to(REPO)), "title": f"Lab exercise: {f.parent.name}",
                    "solution": str((f.parent / "Solution.lean").relative_to(REPO))})
    for name, path in EXAM_PARTS.items():
        out.append({"path": path, "title": f"Ibex exam: {name}", "solution": None})
    return out


@app.get("/api/workbook")
def workbook() -> List[dict]:
    return [{**w, "text": (REPO / w["path"]).read_text()} for w in _workbook()]


class WorkbookSave(BaseModel):
    path: str = Field(max_length=200)
    text: str = Field(max_length=400_000)


@app.post("/api/workbook/save")
def workbook_save(req: WorkbookSave) -> dict:
    """Save one of your exercise or exam files: the only files the app writes in the repository."""
    allowed = {w["path"] for w in _workbook()}
    if req.path not in allowed:
        raise HTTPException(403, f"{req.path} is not one of your exercise files")
    (REPO / req.path).write_text(req.text)
    return {"saved": req.path, "bytes": len(req.text.encode())}


# ----------------------------------------------------------------------- Ibex exam
EXAM_PARTS = {"MultDiv": "RtlProof/Exam/Ibex/MultDiv.lean", "LoadStore": "RtlProof/Exam/Ibex/LoadStore.lean"}


@app.get("/api/exam")
def exam_files() -> dict:
    """Your two exam files and the items in each (statements in RtlProof/Exam/Ibex/Statements.lean)."""
    from pvs_exam.__main__ import ITEMS
    return {"parts": [{"name": n, "path": p, "text": (REPO / p).read_text()} for n, p in EXAM_PARTS.items()],
            "items": [{"name": k, "part": v[0], "points": v[1], "title": v[2]} for k, v in ITEMS.items()]}


class ExamSave(BaseModel):
    part: str = Field(pattern=r"^(MultDiv|LoadStore)$")
    text: str = Field(max_length=400_000)


@app.post("/api/exam/save")
def exam_save(req: ExamSave) -> dict:
    """Save one of your exam files (the only files the app writes in the repository)."""
    path = REPO / EXAM_PARTS[req.part]
    path.write_text(req.text)
    return {"saved": EXAM_PARTS[req.part], "bytes": len(req.text.encode())}


@app.post("/api/exam/grade")
def exam_grade() -> dict:
    """`pvs-exam`: which statements the saved files prove, and with what."""
    from pvs_exam.__main__ import grade
    return grade()


@app.get("/api/status")
def status() -> dict:
    lake = os.environ.get("LAKE") or shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
    return {
        "lean": Path(lake).exists() or bool(shutil.which("lake")),
        "sby": bool(shutil.which("sby") or shutil.which("yowasp-sby")),
        "tutor": _have_key(),
        "ibex": (REPO / "third_party/ibex/rtl").is_dir(),
    }


@app.get("/")
def index() -> FileResponse:
    return FileResponse(STATIC / "index.html")


app.mount("/static", StaticFiles(directory=STATIC), name="static")


def main() -> None:
    import argparse
    import uvicorn
    ap = argparse.ArgumentParser(prog="pvs-app")
    ap.add_argument("--host", default="127.0.0.1", help="use 0.0.0.0 only inside a container")
    ap.add_argument("--port", type=int, default=8000)
    a = ap.parse_args()
    uvicorn.run(app, host=a.host, port=a.port)


if __name__ == "__main__":
    main()
