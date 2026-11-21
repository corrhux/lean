"""UNSAT certificates: DRUP proofs and a forward RUP checker (course chapter B5).

A SAT answer is self-certifying: plug the model in and check every clause.
An UNSAT answer is not — so modern solvers emit a *proof*: the sequence of
clauses they learned (and deleted). Each learned clause must follow from the
current clause set by **reverse unit propagation (RUP)**: assume the clause is
false, unit-propagate, and a conflict must appear. If the empty clause is
eventually derived, the formula is unsatisfiable.

This checker is intentionally simple (forward checking, naive propagation).
Industrial checkers (drat-trim, cake_lpr, Lean's LRAT checker inside
``bv_decide``) add RAT steps, backward checking, and hints (LRAT) for speed —
and some are themselves formally verified.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Optional, Sequence, Tuple

from .cnf import CNF

Step = Tuple[str, List[int]]


@dataclass
class CheckResult:
    ok: bool
    steps_checked: int
    message: str


def parse_drup(text: str) -> List[Step]:
    steps: List[Step] = []
    for raw in text.splitlines():
        line = raw.strip()
        if not line or line.startswith("c"):
            continue
        kind = "a"
        if line.startswith("d "):
            kind, line = "d", line[2:]
        lits = [int(t) for t in line.split()]
        if not lits or lits[-1] != 0:
            raise ValueError(f"proof line not 0-terminated: {raw!r}")
        steps.append((kind, lits[:-1]))
    return steps


def _rup(clauses: Sequence[List[int]], clause: Sequence[int]) -> bool:
    """Does unit propagation on clauses ∧ ¬clause reach a conflict?"""
    assign: Dict[int, bool] = {}
    for l in clause:
        if assign.get(abs(l)) is (l > 0):
            return True                    # clause contains l and ¬l: tautology
        assign[abs(l)] = l < 0             # make literal false
    changed = True
    while changed:
        changed = False
        for c in clauses:
            unassigned: Optional[int] = None
            n_un = 0
            sat = False
            for l in c:
                v = assign.get(abs(l))
                if v is None:
                    n_un += 1
                    unassigned = l
                elif v == (l > 0):
                    sat = True
                    break
            if sat:
                continue
            if n_un == 0:
                return True
            if n_un == 1:
                assert unassigned is not None
                assign[abs(unassigned)] = unassigned > 0
                changed = True
    return False


def check_drup(cnf: CNF, steps: Sequence[Step]) -> CheckResult:
    db: List[List[int]] = [list(c) for c in cnf.clauses]
    for i, (kind, lits) in enumerate(steps):
        if kind == "d":
            key = sorted(lits)
            for j, c in enumerate(db):
                if sorted(c) == key:
                    del db[j]
                    break
            continue
        if not _rup(db, lits):
            return CheckResult(False, i, f"step {i}: clause {lits} is not RUP")
        if not lits:
            return CheckResult(True, i + 1, "empty clause derived: UNSAT verified")
        db.append(list(lits))
    if _rup(db, []):
        return CheckResult(True, len(steps), "empty clause is RUP: UNSAT verified")
    return CheckResult(False, len(steps), "proof ended without deriving the empty clause")
