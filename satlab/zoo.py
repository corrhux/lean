"""The solver zoo: run one CNF through many solvers and compare (course B3).

Real solvers come from PySAT (MiniSat, Glucose, CaDiCaL, Kissat, Lingeling,
Maple*, MergeSat …) and Z3. The teaching DPLL/CDCL from this package run in
the same harness so the gap between a textbook solver and an engineered one
is visible.

Every solver runs in its own process, so a hard instance can be cut off by a
wall-clock timeout regardless of whether the solver supports interruption.
"""

from __future__ import annotations

import multiprocessing as mp
import time
from typing import Dict, List, Optional, Sequence

from .cnf import CNF

DEFAULT_SOLVERS = [
    "minisat22", "glucose4", "maplechrono", "lingeling",
    "cadical195", "kissat404", "z3", "teach-cdcl", "teach-dpll",
]

LINEAGE = {
    "minisat22": "MiniSat 2.2 (2003–): compact reference CDCL, assumptions API",
    "minisatep": "MiniSat (extended)",
    "glucose3": "Glucose 3: LBD-based clause management",
    "glucose4": "Glucose 4: LBD-based clause management",
    "glucose42": "Glucose 4.2",
    "maplesat": "MapleSAT: learning-rate branching (LRB)",
    "maplechrono": "Maple + chronological backtracking",
    "maplecm": "Maple COMiniSatPS variant",
    "mergesat3": "MergeSat: MiniSat lineage + merged techniques",
    "lingeling": "Lingeling: heavy inprocessing",
    "cadical103": "CaDiCaL 1.0.3",
    "cadical153": "CaDiCaL 1.5.3",
    "cadical195": "CaDiCaL 1.9.5: inprocessing, proof output (used by Lean bv_decide)",
    "cadical300": "CaDiCaL 3.0",
    "kissat404": "Kissat 4.0.4: CaDiCaL ideas re-engineered for speed",
    "z3": "Z3: SMT solver (CDCL(T)); here on pure CNF",
    "teach-cdcl": "satlab teaching CDCL (Python)",
    "teach-dpll": "satlab textbook DPLL (Python)",
}


def _worker(name: str, num_vars: int, clauses: List[List[int]], q: "mp.Queue") -> None:
    t0 = time.perf_counter()
    row: Dict[str, object] = {"solver": name}
    try:
        if name == "z3":
            import z3

            s = z3.Solver()
            xs = [None] + [z3.Bool(f"v{i}") for i in range(1, num_vars + 1)]
            for c in clauses:
                s.add(z3.Or([xs[l] if l > 0 else z3.Not(xs[-l]) for l in c]) if c else z3.BoolVal(False))
            res = s.check()
            row["result"] = {z3.sat: "SAT", z3.unsat: "UNSAT"}.get(res, "UNKNOWN")
            st = s.statistics()
            for key in ("conflicts", "decisions", "propagations"):
                if key in st.keys():
                    row[key] = st.get_key_value(key)
        elif name.startswith("teach-"):
            cnf = CNF(num_vars, clauses)
            if name == "teach-cdcl":
                from . import cdcl

                r = cdcl.solve(cnf)
                row.update(conflicts=r.stats.conflicts, decisions=r.stats.decisions,
                           propagations=r.stats.propagations)
            else:
                from . import dpll

                r = dpll.solve(cnf)
                row.update(conflicts=r.stats.conflicts, decisions=r.stats.decisions,
                           propagations=r.stats.propagations)
            row["result"] = {True: "SAT", False: "UNSAT", None: "UNKNOWN"}[r.sat]
        else:
            from pysat.solvers import Solver

            with Solver(name=name, bootstrap_with=clauses) as s:
                ok = s.solve()
                row["result"] = "SAT" if ok else "UNSAT"
                try:
                    row.update(s.accum_stats())
                except NotImplementedError:
                    pass
    except Exception as e:  # report, don't crash the zoo
        row["result"] = "ERROR"
        row["error"] = f"{type(e).__name__}: {e}"
    row["time_s"] = round(time.perf_counter() - t0, 4)
    q.put(row)


def run(cnf: CNF, solvers: Sequence[str] = DEFAULT_SOLVERS, timeout: float = 30.0) -> List[Dict[str, object]]:
    ctx = mp.get_context("fork")
    rows = []
    for name in solvers:
        q: "mp.Queue" = ctx.Queue()
        p = ctx.Process(target=_worker, args=(name, cnf.num_vars, cnf.clauses, q))
        t0 = time.perf_counter()
        p.start()
        p.join(timeout)
        if p.is_alive():
            p.kill()
            p.join()
            rows.append({"solver": name, "result": "TIMEOUT",
                         "time_s": round(time.perf_counter() - t0, 2)})
        else:
            rows.append(q.get() if not q.empty() else {"solver": name, "result": "CRASH"})
    return rows


def table(rows: Sequence[Dict[str, object]]) -> str:
    cols = ["solver", "result", "time_s", "conflicts", "decisions", "propagations"]
    data = [[str(r.get(c, "")) for c in cols] for r in rows]
    widths = [max(len(c), *(len(d[i]) for d in data)) for i, c in enumerate(cols)]
    fmt = "  ".join("{:<%d}" % w for w in widths)
    out = [fmt.format(*cols), fmt.format(*("-" * w for w in widths))]
    out += [fmt.format(*d) for d in data]
    return "\n".join(out)


def consistent(rows: Sequence[Dict[str, object]]) -> Optional[str]:
    """All solvers that finished must agree; returns the shared verdict or None."""
    verdicts = {r["result"] for r in rows if r["result"] in ("SAT", "UNSAT")}
    if len(verdicts) > 1:
        raise AssertionError(f"solvers disagree: {rows}")
    return verdicts.pop() if verdicts else None
