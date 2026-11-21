"""Textbook DPLL (Davis–Putnam–Logemann–Loveland, 1962).

Deliberately naive, for contrast with ``cdcl.py``:

* unit propagation rescans every clause (no watched literals),
* branching picks the lowest-numbered unassigned variable, trying ``False`` first,
* on conflict it backtracks *chronologically* to the most recent decision whose
  other branch is untried — it learns nothing, so it can rediscover the same
  conflict many times.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

from .cnf import CNF
from .trace import Trace


@dataclass
class DPLLStats:
    decisions: int = 0
    propagations: int = 0
    conflicts: int = 0
    backtracks: int = 0


@dataclass
class DPLLResult:
    sat: Optional[bool]
    model: Dict[int, bool] = field(default_factory=dict)
    stats: DPLLStats = field(default_factory=DPLLStats)


def solve(cnf: CNF, trace: Optional[Trace] = None, max_conflicts: Optional[int] = None) -> DPLLResult:
    tr = trace or Trace(enabled=False)
    stats = DPLLStats()
    assign: Dict[int, bool] = {}
    # trail entries: (literal, is_branch_point, other_branch_tried)
    trail: List[Tuple[int, bool, bool]] = []

    def value(lit: int) -> Optional[bool]:
        v = assign.get(abs(lit))
        if v is None:
            return None
        return v if lit > 0 else not v

    def level() -> int:
        return sum(1 for _, is_dec, _ in trail if is_dec)

    def set_lit(lit: int, is_dec: bool, tried: bool) -> None:
        assign[abs(lit)] = lit > 0
        trail.append((lit, is_dec, tried))

    def propagate() -> Optional[List[int]]:
        changed = True
        while changed:
            changed = False
            for c in cnf.clauses:
                unassigned = None
                n_unassigned = 0
                satisfied = False
                for l in c:
                    v = value(l)
                    if v is True:
                        satisfied = True
                        break
                    if v is None:
                        n_unassigned += 1
                        unassigned = l
                if satisfied:
                    continue
                if n_unassigned == 0:
                    return c
                if n_unassigned == 1:
                    assert unassigned is not None
                    set_lit(unassigned, False, False)
                    stats.propagations += 1
                    tr.emit("propagate", lit=unassigned, level=level(), reason=list(c))
                    changed = True
        return None

    while True:
        confl = propagate()
        if confl is not None:
            stats.conflicts += 1
            tr.emit("conflict", clause=list(confl), level=level())
            if max_conflicts is not None and stats.conflicts > max_conflicts:
                tr.emit("result", sat=None)
                return DPLLResult(None, stats=stats)
            # chronological backtracking: undo to the latest untried branch point
            while trail and not (trail[-1][1] and not trail[-1][2]):
                lit, _, _ = trail.pop()
                del assign[abs(lit)]
            if not trail:
                tr.emit("result", sat=False)
                return DPLLResult(False, stats=stats)
            lit, _, _ = trail.pop()
            del assign[abs(lit)]
            stats.backtracks += 1
            tr.emit("backtrack", to=level())
            set_lit(-lit, True, True)
            tr.emit("flip", lit=-lit, level=level())
            continue

        free = next((v for v in range(1, cnf.num_vars + 1) if v not in assign), None)
        if free is None:
            tr.emit("result", sat=True)
            model = {v: assign.get(v, False) for v in range(1, cnf.num_vars + 1)}
            return DPLLResult(True, model, stats)
        stats.decisions += 1
        set_lit(-free, True, False)
        tr.emit("decide", lit=-free, level=level())
