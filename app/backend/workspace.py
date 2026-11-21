"""Twin workspace: edit a design's RTL and Lean solution, then re-run both sides.

Edits never touch the repository's files. They are written to
`build/app/work/<design>/` and checked there:

* model checking: SymbiYosys on the edited RTL (`ftwin`'s `run_sby`);
* Lean: if the RTL changed, `sv2lean` regenerates the model and one Lean
  document is assembled: the merged imports, the regenerated model, then the
  (edited) solution with its own `import` lines commented out. Without RTL
  edits the solution imports the committed model as usual.

The same document backs the live editor, so goals and errors reflect the
edited RTL. `prefix_lines` is how many lines precede the solution text.
"""

from __future__ import annotations

import hashlib
import os
import re
import shutil
import subprocess
import sys
import tomllib
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional

REPO = Path(__file__).resolve().parents[2]
WORK = REPO / "build" / "app" / "work"
sys.path.insert(0, str(REPO / "tools"))
from ftwin.__main__ import check_theorems, run_sby  # noqa: E402


class WorkspaceError(Exception):
    pass


def config(name: str) -> dict:
    p = REPO / "rtl" / name / "twin.toml"
    if not p.is_file():
        raise WorkspaceError(f"unknown design {name!r}")
    return tomllib.loads(p.read_text())


def solution_path(cfg: dict) -> Path:
    module = cfg["lean"]["module"]
    return REPO / (module.replace(".", "/") + ".lean")


def generated_module(cfg: dict) -> str:
    return cfg["lean"]["generated"].removesuffix(".lean").replace("/", ".")


def _check_edits(name: str, cfg: dict, rtl: Dict[str, str]) -> Dict[str, str]:
    """Keep only edits to the design's own RTL files that differ from the committed text."""
    out = {}
    for f, text in (rtl or {}).items():
        if f not in cfg["files"]:
            raise WorkspaceError(f"{f!r} is not one of this design's RTL files {cfg['files']}")
        if len(text) > 200_000:
            raise WorkspaceError(f"{f} is too large")
        if text != (REPO / "rtl" / name / f).read_text():
            out[f] = text
    return out


def write_sources(name: str, cfg: dict, rtl: Dict[str, str]) -> Path:
    """Copy the design directory to the workspace and apply the edits."""
    src = WORK / name / "src"
    if src.exists():
        shutil.rmtree(src)
    root = REPO / "rtl" / name
    shutil.copytree(root, src, ignore=lambda d, names: [n for n in names if (Path(d) / n).is_dir()])
    for f, text in rtl.items():
        (src / f).write_text(text)
    return src


def regenerate(name: str, cfg: dict, rtl: Dict[str, str]) -> str:
    """Run sv2lean on the edited RTL; return the generated Lean text (cached by content)."""
    key = hashlib.sha256(repr(sorted(rtl.items())).encode()).hexdigest()[:16]
    out = WORK / name / f"model_{key}.lean"
    if out.exists():
        return out.read_text()
    src = write_sources(name, cfg, rtl)
    cmd = [sys.executable, "-m", "sv2lean", *[str(src / f) for f in cfg["files"]], "--top", cfg["top"],
           *cfg["lean"].get("sv2lean_args", []), "--namespace", cfg["lean"]["namespace"], "-o", str(out)]
    p = subprocess.run(cmd, cwd=REPO, capture_output=True, text=True, timeout=600,
                       env={**os.environ, "PYTHONPATH": str(REPO / "tools")})
    if p.returncode != 0 or not out.exists():
        msg = (p.stdout + p.stderr).strip().splitlines()
        raise WorkspaceError("sv2lean could not translate the edited RTL:\n" + "\n".join(msg[-15:]))
    return out.read_text()


@dataclass
class Document:
    text: str
    prefix_lines: int
    regenerated: bool


def _split_imports(text: str):
    imports, body = [], []
    for line in text.splitlines():
        (imports if line.startswith("import ") else body).append(line)
    return imports, body


def assemble(name: str, solution: Optional[str] = None, rtl: Optional[Dict[str, str]] = None) -> Document:
    cfg = config(name)
    solution = solution if solution is not None else solution_path(cfg).read_text()
    edits = _check_edits(name, cfg, rtl or {})
    if not edits:
        return Document(solution, 0, False)
    model = regenerate(name, cfg, edits)
    gen_mod = generated_module(cfg)
    m_imports, m_body = _split_imports(model)
    s_imports = [l for l in solution.splitlines() if l.startswith("import ")]
    imports = list(dict.fromkeys(m_imports + [l for l in s_imports if l.split()[1] != gen_mod]))
    header = imports + [f"-- The model below was regenerated from your edited RTL (replaces {gen_mod})."] + m_body + [
        "", "-- ===== your solution ====="]
    sol = ["-- " + l if l.startswith("import ") else l for l in solution.splitlines()]
    return Document("\n".join(header + sol) + "\n", len(header), True)


def run(name: str, rtl: Optional[Dict[str, str]] = None, solution: Optional[str] = None) -> List[dict]:
    """Both sides on the edited design: every SymbiYosys task and every Lean theorem."""
    from dataclasses import asdict
    cfg = config(name)
    edits = _check_edits(name, cfg, rtl or {})
    asserts = sorted(cfg["lean"].get("theorems", {}).keys())
    src = write_sources(name, cfg, edits)
    rundir = WORK / name / "run"
    if rundir.exists():
        shutil.rmtree(rundir)
    rundir.mkdir(parents=True)
    results = run_sby(name, src, cfg, asserts, rundir)
    try:
        doc = assemble(name, solution, edits)
        lean = check_theorems(name, doc.text, cfg["lean"]["theorems"], asserts)
        for r in lean:                       # point error positions at the solution's own lines
            r.note = re.sub(r"\S+\.lean:(\d+):(\d+): ",
                            lambda m: f"solution line {int(m[1]) - doc.prefix_lines}: ", r.note or "")
        results += lean
    except WorkspaceError as e:
        from ftwin.__main__ import Result
        results += [Result(name, "lean", "lean", a, "error", note=str(e)[:400]) for a in asserts]
    rows = [asdict(r) for r in results]
    for r in rows:
        if r.get("cex_vcd"):
            r["cex_vcd"] = str(Path(r["cex_vcd"]).resolve().relative_to(REPO))
    return rows
