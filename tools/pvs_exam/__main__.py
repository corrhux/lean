"""Grade the Ibex exam: which statements your files prove, and with what.

    pvs-exam                       # grade RtlProof/Exam/Ibex/{MultDiv,LoadStore}.lean
    pvs-exam --json out.json       # also write the result as JSON
    pvs-exam --reference           # grade the reference solutions (capstone/exam/solutions)
    pvs-exam --hashes              # print the hashes of the protected files

For each item the grader appends, to a copy of your file,

    example : IbexExam.Stmt.<item> := IbexExam.<item>   -- same statement as the exam's
    #print axioms IbexExam.<item>                       -- what the proof relies on

and compiles it with `lake env lean`. An item scores when the `example` type-checks and
the axioms are only Lean's three (`propext`, `Classical.choice`, `Quot.sound`) plus the
ones `bv_decide` adds for its SAT certificates. `sorry`, `native_decide` or an `axiom`
of your own does not score.

The statements only mean what the exam says together with the definitions they use, so
the grader also checks that `Spec.lean`, `Statements.lean` and the generated models are
unchanged (by hash); if not, the result is marked unofficial.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Dict, List, Optional

REPO = Path(__file__).resolve().parents[2]
EXAM = REPO / "RtlProof" / "Exam" / "Ibex"
SOLUTIONS = REPO / "capstone" / "exam" / "solutions"

# item -> (part file stem, points, short title)
ITEMS: Dict[str, tuple] = {
    "md_state_valid": ("MultDiv", 10, "M1 FSM state always valid"),
    "mul_latency": ("MultDiv", 15, "M2 multiply takes 32 cycles"),
    "div_latency": ("MultDiv", 10, "M3 divide takes 36 cycles"),
    "constant_time": ("MultDiv", 20, "M4 data-independent timing"),
    "mul_correct": ("MultDiv", 0, "challenge: multiplier computes a * b"),
    "lsu_req_held": ("LoadStore", 5, "L1 request held until granted"),
    "lsu_store": ("LoadStore", 15, "L2 stores write what the ISA says"),
    "lsu_load": ("LoadStore", 15, "L3 loads, any memory latency"),
    "lsu_load_misaligned": ("LoadStore", 10, "L4 misaligned word load"),
}
PARTS = ["MultDiv", "LoadStore"]

# Files whose meaning the statements depend on, with their expected SHA-256.
PROTECTED = {
    "RtlProof/Exam/Ibex/Spec.lean": "",
    "RtlProof/Exam/Ibex/Statements.lean": "",
    "RtlProof/Generated/IbexMD.lean": "",
    "RtlProof/Generated/IbexLSU.lean": "",
    "RtlProof/Generated/IbexAlu.lean": "",
    "RtlProof/Core/Circuit.lean": "",
}
HASHES_FILE = REPO / "capstone" / "exam" / "protected.sha256"

STD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


@dataclass
class Item:
    name: str
    title: str
    points: int
    status: str                 # proved | sorry | failed | missing | untrusted | not graded
    score: int = 0
    axioms: List[str] = field(default_factory=list)
    detail: str = ""


def lake() -> str:
    return os.environ.get("LAKE") or shutil.which("lake") or str(Path.home() / ".elan/bin/lake")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def expected_hashes() -> Dict[str, str]:
    out = {}
    for line in HASHES_FILE.read_text().splitlines():
        if line.strip() and not line.startswith("#"):
            h, f = line.split(maxsplit=1)
            out[f.strip()] = h
    return out


def tampered() -> List[str]:
    exp = expected_hashes()
    return [f for f in PROTECTED if not (REPO / f).is_file() or sha256(REPO / f) != exp.get(f)]


def _theorem_spans(text: str) -> Dict[str, tuple]:
    """Line range (1-based, inclusive) of each top-level theorem/lemma in the file."""
    starts = [(i + 1, m.group(1)) for i, line in enumerate(text.splitlines())
              for m in [re.match(r"\s*(?:@\[[^\]]*\]\s*)?(?:private\s+)?(?:theorem|lemma)\s+([\w.']+)", line)] if m]
    n = len(text.splitlines())
    spans = {}
    for k, (line, name) in enumerate(starts):
        end = starts[k + 1][0] - 1 if k + 1 < len(starts) else n
        spans[name.split(".")[-1]] = (line, end)
    return spans


def grade_file(path: Path, part: str) -> List[Item]:
    text = path.read_text()
    names = [n for n, (p, _, _) in ITEMS.items() if p == part]
    probe = text.rstrip("\n") + "\n\n-- ===== added by pvs-exam =====\n"
    for n in names:
        probe += f"example : IbexExam.Stmt.{n} := IbexExam.{n}\n#print axioms IbexExam.{n}\n"
    work = REPO / "build" / "exam"
    work.mkdir(parents=True, exist_ok=True)
    tmp = work / f"grade_{part}.lean"
    tmp.write_text(probe)
    p = subprocess.run([lake(), "env", "lean", str(tmp)], cwd=REPO, capture_output=True, text=True,
                       timeout=3600)
    out = p.stdout + p.stderr
    n_src = len(text.splitlines())
    spans = _theorem_spans(text)
    errors = [(int(m.group(1)), m.group(3)) for m in
              re.finditer(r"^\S+?:(\d+):(\d+): error: (.*)$", out, re.M)]
    items = []
    for n in names:
        _, pts, title = ITEMS[n]
        it = Item(n, title, pts, "missing")
        m = re.search(rf"'IbexExam\.{re.escape(n)}' depends on axioms: \[([^\]]*)\]", out, re.S)
        none = f"'IbexExam.{n}' does not depend on any axioms" in out
        # errors from our appended `example` lines mean the theorem is missing or its statement differs
        probe_errs = [msg for ln, msg in errors if ln > n_src and f"IbexExam.{n}" in probe.splitlines()[ln - 1]]
        if not (m or none) or probe_errs:
            it.status = "open" if pts == 0 else "missing"
            it.detail = (probe_errs[0] if probe_errs else f"no theorem IbexExam.{n}")[:300]
            items.append(it)
            continue
        ax = [] if none else [a.strip() for a in m.group(1).replace("\n", " ").split(",") if a.strip()]
        it.axioms = ax
        own_errs = [msg for ln, msg in errors if n in spans and spans[n][0] <= ln <= spans[n][1]]
        extra = [a for a in ax if a not in STD_AXIOMS and "._native.bv_decide." not in a]
        if "sorryAx" in ax:
            it.status = "failed" if own_errs else "sorry"
            it.detail = own_errs[0][:300] if own_errs else "uses sorry (directly or through a lemma)"
        elif extra:
            it.status = "untrusted"
            it.detail = "relies on " + ", ".join(extra)
        else:
            it.status = "proved"
            it.score = pts
        items.append(it)
    return items


def grade(reference: bool = False) -> dict:
    folder = SOLUTIONS if reference else EXAM
    subprocess.run([lake(), "build", "RtlProof.Exam.Ibex.Statements", "RtlProof.Meta.Induction"],
                   cwd=REPO, capture_output=True, text=True)
    items: List[Item] = []
    for part in PARTS:
        f = folder / f"{part}.lean"
        if f.is_file():
            items += grade_file(f, part)
        else:
            items += [Item(n, t, p, "missing", detail=f"no file {f.relative_to(REPO)}")
                      for n, (pp, p, t) in ITEMS.items() if pp == part]
    total = sum(v[1] for v in ITEMS.values())
    return {"items": [asdict(i) for i in items], "score": sum(i.score for i in items), "total": total,
            "tampered": tampered(), "reference": reference}


def report(r: dict) -> str:
    rows = [("item", "points", "status", "notes")]
    for i in r["items"]:
        pts = f"{i['score']}/{i['points']}" if i["points"] else "bonus"
        note = i["detail"] or ("kernel + bv_decide" if i["status"] == "proved" else "")
        rows.append((i["title"], pts, i["status"], note.splitlines()[0][:70] if note else ""))
    w = [max(len(r_[k]) for r_ in rows) for k in range(4)]
    lines = ["  ".join(c.ljust(w[k]) for k, c in enumerate(row)) for row in rows]
    lines.insert(1, "  ".join("-" * x for x in w))
    lines.append(f"\nscore: {r['score']} / {r['total']}")
    if r["tampered"]:
        lines.append("UNOFFICIAL: these protected files changed, so the statements may not mean what "
                     "the exam says: " + ", ".join(r["tampered"]))
    return "\n".join(lines)


def main(argv: Optional[List[str]] = None) -> int:
    ap = argparse.ArgumentParser(prog="pvs-exam", description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--reference", action="store_true", help="grade the reference solutions")
    ap.add_argument("--json", help="write the result as JSON")
    ap.add_argument("--hashes", action="store_true", help="print the protected files' hashes")
    a = ap.parse_args(argv)
    if a.hashes:
        for f in PROTECTED:
            print(f"{sha256(REPO / f)}  {f}")
        return 0
    r = grade(a.reference)
    print(report(r))
    if a.json:
        Path(a.json).parent.mkdir(parents=True, exist_ok=True)
        Path(a.json).write_text(json.dumps(r, indent=2))
    if a.reference:   # CI: every graded item must be proved, and nothing tampered
        return 0 if r["score"] == r["total"] and not r["tampered"] else 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
