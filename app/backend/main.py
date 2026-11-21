"""Proof vs. Search web app: a local, offline API over the course tools (SPEC §6.7).

    pip install -e ".[app]"
    pvs-app                      # http://127.0.0.1:8000  (localhost only by default)

Every endpoint wraps an existing command-line tool, so the app and the CLI
always agree: `ftwin run`, `satlab gen`/`zoo`, the tutor's `check_lean`,
`read_file` and `cex_summary`.
"""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import sys
import tomllib
from pathlib import Path
from typing import Dict, List, Optional

from fastapi import FastAPI, HTTPException
from fastapi.responses import FileResponse, PlainTextResponse
from fastapi.staticfiles import StaticFiles
from pydantic import BaseModel, Field

REPO = Path(__file__).resolve().parents[2]
STATIC = Path(__file__).resolve().parents[1] / "frontend"
RESULTS = REPO / "build" / "app"

sys.path.insert(0, str(REPO / "tools"))
from tutor import tools as ttools  # noqa: E402

app = FastAPI(title="Proof vs. Search", docs_url="/api/docs")


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


@app.post("/api/designs/{name}/run")
def run_design(name: str) -> List[dict]:
    """Run both sides (`ftwin run`): every SymbiYosys task and every Lean theorem."""
    if name not in _designs():
        raise HTTPException(404, f"unknown design {name!r}")
    RESULTS.mkdir(parents=True, exist_ok=True)
    out = RESULTS / f"{name}.json"
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


class LeanCheck(BaseModel):
    code: str = Field(max_length=200_000)


@app.post("/api/lean/check")
def lean_check(req: LeanCheck) -> dict:
    """Compile a snippet in the project (the tutor's `check_lean`)."""
    return ttools.check_lean(req.code)


DOCS = ["course/README.md", "docs/LEAN_FLUENCY.md", "docs/COURSE.md", "docs/CAPSTONE_PRIMER.md",
        "docs/CAPSTONE_IBEX.md", "capstone/ibex/README.md", "satlab/README.md", "docs/SPEC.md",
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


class TutorRequest(BaseModel):
    question: str = Field(max_length=10_000)
    file: Optional[str] = None
    level: int = Field(2, ge=1, le=5)


@app.post("/api/tutor")
def tutor(req: TutorRequest) -> dict:
    if not (os.environ.get("ANTHROPIC_API_KEY") or os.environ.get("ANTHROPIC_AUTH_TOKEN")):
        raise HTTPException(503, "The tutor needs ANTHROPIC_API_KEY. Everything else works without it.")
    from tutor.client import Tutor
    from tutor.prompts import user_message
    turn = Tutor().ask(user_message(req.question, req.level, req.file))
    return {"text": turn.text, "tools": turn.tool_calls, "model": turn.served_by}


@app.get("/api/status")
def status() -> dict:
    lake = os.environ.get("LAKE") or shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
    return {
        "lean": Path(lake).exists() or bool(shutil.which("lake")),
        "sby": bool(shutil.which("sby") or shutil.which("yowasp-sby")),
        "tutor": bool(os.environ.get("ANTHROPIC_API_KEY") or os.environ.get("ANTHROPIC_AUTH_TOKEN")),
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
