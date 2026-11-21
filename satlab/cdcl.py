"""A teaching CDCL SAT solver.

Readable rather than fast, but it implements the real techniques, each of
which can be switched off to *see* what it buys (course chapter B2):

* two watched literals (Chaff, 2001) — cheap unit propagation
* conflict analysis to the first unique implication point (1UIP, GRASP 1996)
* non-chronological backjumping
* branching: EVSIDS (MiniSat-style exponential VSIDS), fixed order, or random
* restarts: none, Luby sequence, or Glucose-style dynamic (LBD moving average)
* phase saving
* learned-clause minimisation (local, using reason clauses)
* learned-clause database reduction by LBD ("glue", Glucose 2009)
* assumptions for incremental solving (MiniSat API style) — the mechanism BMC
  and IC3/PDR engines rely on (chapter B4)
* DRUP proof output (learned clauses + deletions), checkable by ``certs.py``
  or drat-trim (chapter B5)

Internally a literal is encoded as ``2*v`` (positive) or ``2*v+1`` (negative);
the public API uses DIMACS integers.
"""

from __future__ import annotations

import heapq
import random
from collections import deque
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Sequence, Tuple

from .cnf import CNF
from .trace import Trace

UNDEF, FALSE, TRUE = -1, 0, 1


def _enc(lit: int) -> int:
    return 2 * abs(lit) + (1 if lit < 0 else 0)


def _dec(ilit: int) -> int:
    v = ilit >> 1
    return -v if ilit & 1 else v


@dataclass
class Options:
    branching: str = "vsids"        # "vsids" | "ordered" | "random"
    restarts: str = "luby"          # "none" | "luby" | "glucose"
    luby_unit: int = 100            # conflicts per Luby unit
    phase_saving: bool = True
    minimize: bool = True
    reduce: bool = True             # LBD-based learned-clause deletion
    var_decay: float = 0.95
    seed: int = 0
    proof: bool = False             # record a DRUP proof


@dataclass
class Stats:
    decisions: int = 0
    propagations: int = 0
    conflicts: int = 0
    learned: int = 0
    learned_literals: int = 0
    deleted: int = 0
    restarts: int = 0
    max_level: int = 0


@dataclass
class Result:
    sat: Optional[bool]                      # None: conflict limit reached
    model: Dict[int, bool] = field(default_factory=dict)
    stats: Stats = field(default_factory=Stats)
    failed_assumptions: List[int] = field(default_factory=list)


class _Clause:
    __slots__ = ("lits", "learnt", "lbd", "deleted")

    def __init__(self, lits: List[int], learnt: bool, lbd: int = 0):
        self.lits = lits
        self.learnt = learnt
        self.lbd = lbd
        self.deleted = False


def luby(i: int) -> int:
    """i-th element (0-based) of the Luby sequence 1,1,2,1,1,2,4,1,1,2,..."""
    size, seq = 1, 0
    while size < i + 1:
        seq += 1
        size = 2 * size + 1
    while size - 1 != i:
        size = (size - 1) >> 1
        seq -= 1
        i = i % size
    return 1 << seq


class Solver:
    def __init__(self, cnf: Optional[CNF] = None, options: Optional[Options] = None,
                 trace: Optional[Trace] = None):
        self.opt = options or Options()
        self.trace = trace or Trace(enabled=False)
        self.stats = Stats()
        self.rng = random.Random(self.opt.seed)
        self.n = 0
        self.value: List[int] = [UNDEF]
        self.level: List[int] = [0]
        self.reason: List[Optional[_Clause]] = [None]
        self.activity: List[float] = [0.0]
        self.saved_phase: List[bool] = [False]
        self.seen: List[bool] = [False]
        self.watches: List[List[_Clause]] = [[], []]
        self.trail: List[int] = []
        self.trail_lim: List[int] = []
        self.qhead = 0
        self.clauses: List[_Clause] = []
        self.learnts: List[_Clause] = []
        self.var_inc = 1.0
        self.heap: List[Tuple[float, int]] = []
        self.ok = True
        self.proof: List[Tuple[str, List[int]]] = []
        self.max_learnts = 0.0
        self.lbd_recent: deque = deque(maxlen=50)
        self.lbd_sum = 0
        self.lbd_count = 0
        if cnf is not None:
            self.ensure_vars(cnf.num_vars)
            for c in cnf.clauses:
                self.add_clause(c)

    # ------------------------------------------------------------ setup
    def ensure_vars(self, n: int) -> None:
        while self.n < n:
            self.n += 1
            self.value.append(UNDEF)
            self.level.append(0)
            self.reason.append(None)
            self.activity.append(0.0)
            self.saved_phase.append(False)
            self.seen.append(False)
            self.watches.extend(([], []))
            heapq.heappush(self.heap, (0.0, self.n))

    def _val(self, ilit: int) -> int:
        v = self.value[ilit >> 1]
        if v == UNDEF:
            return UNDEF
        return v ^ (ilit & 1)

    def decision_level(self) -> int:
        return len(self.trail_lim)

    def add_clause(self, lits: Sequence[int]) -> bool:
        """Add a clause (DIMACS literals). Must be called at decision level 0."""
        assert self.decision_level() == 0, "add clauses between solve() calls only"
        if not self.ok:
            return False
        self.ensure_vars(max((abs(l) for l in lits), default=0))
        seen: Dict[int, bool] = {}
        out: List[int] = []
        for l in lits:
            il = _enc(l)
            if il ^ 1 in seen:
                return True                      # tautology
            if il in seen or self._val(il) == FALSE:
                continue                         # duplicate / false at level 0
            if self._val(il) == TRUE:
                return True                      # already satisfied at level 0
            seen[il] = True
            out.append(il)
        if not out:
            self.ok = False
            return False
        if len(out) == 1:
            self._enqueue(out[0], None)
            if self._propagate() is not None:
                self.ok = False
            return self.ok
        c = _Clause(out, learnt=False)
        self.clauses.append(c)
        self._attach(c)
        return True

    def _attach(self, c: _Clause) -> None:
        self.watches[c.lits[0]].append(c)
        self.watches[c.lits[1]].append(c)

    # -------------------------------------------------------- assignment
    def _enqueue(self, ilit: int, reason: Optional[_Clause]) -> None:
        v = ilit >> 1
        self.value[v] = TRUE if not (ilit & 1) else FALSE
        self.level[v] = self.decision_level()
        self.reason[v] = reason
        self.trail.append(ilit)

    def _cancel_until(self, lvl: int) -> None:
        if self.decision_level() <= lvl:
            return
        for i in range(len(self.trail) - 1, self.trail_lim[lvl] - 1, -1):
            ilit = self.trail[i]
            v = ilit >> 1
            if self.opt.phase_saving:
                self.saved_phase[v] = not (ilit & 1)
            self.value[v] = UNDEF
            self.reason[v] = None
            if self.opt.branching == "vsids":
                heapq.heappush(self.heap, (-self.activity[v], v))
        del self.trail[self.trail_lim[lvl]:]
        del self.trail_lim[lvl:]
        self.qhead = len(self.trail)

    # ------------------------------------------------- unit propagation
    def _propagate(self) -> Optional[_Clause]:
        """Two-watched-literal propagation. Returns a conflicting clause or None."""
        while self.qhead < len(self.trail):
            p = self.trail[self.qhead]
            self.qhead += 1
            false_lit = p ^ 1
            ws = self.watches[false_lit]
            i = j = 0
            while i < len(ws):
                c = ws[i]
                i += 1
                if c.deleted:
                    continue
                lits = c.lits
                if lits[0] == false_lit:
                    lits[0], lits[1] = lits[1], lits[0]
                if self._val(lits[0]) == TRUE:
                    ws[j] = c
                    j += 1
                    continue
                for k in range(2, len(lits)):
                    if self._val(lits[k]) != FALSE:
                        lits[1], lits[k] = lits[k], lits[1]
                        self.watches[lits[1]].append(c)
                        break
                else:
                    ws[j] = c
                    j += 1
                    if self._val(lits[0]) == FALSE:
                        while i < len(ws):          # keep remaining watchers
                            ws[j] = ws[i]
                            j += 1
                            i += 1
                        del ws[j:]
                        return c
                    self._enqueue(lits[0], c)
                    self.stats.propagations += 1
                    if self.trace.enabled:
                        self.trace.emit("propagate", lit=_dec(lits[0]),
                                        level=self.decision_level(),
                                        reason=[_dec(x) for x in lits])
            del ws[j:]
        return None

    # ------------------------------------------------- conflict analysis
    def _bump(self, v: int) -> None:
        self.activity[v] += self.var_inc
        if self.activity[v] > 1e100:
            for u in range(1, self.n + 1):
                self.activity[u] *= 1e-100
            self.var_inc *= 1e-100
            self.heap = [(-self.activity[u], u) for u in range(1, self.n + 1)
                         if self.value[u] == UNDEF]
            heapq.heapify(self.heap)
        if self.value[v] == UNDEF:
            heapq.heappush(self.heap, (-self.activity[v], v))

    def _analyze(self, confl: _Clause) -> Tuple[List[int], int, int]:
        """1UIP learning. Returns (learned clause, backjump level, LBD)."""
        learnt: List[int] = [-1]       # slot 0 for the asserting (UIP) literal
        counter = 0
        p: Optional[int] = None
        idx = len(self.trail) - 1
        to_clear: List[int] = []
        c: Optional[_Clause] = confl
        while True:
            assert c is not None
            for q in c.lits:
                if p is not None and q == p:
                    continue
                v = q >> 1
                if not self.seen[v] and self.level[v] > 0:
                    self.seen[v] = True
                    to_clear.append(v)
                    if self.opt.branching == "vsids":
                        self._bump(v)
                    if self.level[v] >= self.decision_level():
                        counter += 1
                    else:
                        learnt.append(q)
            while not self.seen[self.trail[idx] >> 1]:
                idx -= 1
            p = self.trail[idx]
            idx -= 1
            c = self.reason[p >> 1]
            self.seen[p >> 1] = False
            counter -= 1
            if counter == 0:
                break
        learnt[0] = p ^ 1

        if self.opt.minimize:
            keep = [learnt[0]]
            for q in learnt[1:]:
                r = self.reason[q >> 1]
                if r is None or any(not self.seen[x >> 1] and self.level[x >> 1] > 0
                                    for x in r.lits if x != q ^ 1):
                    keep.append(q)
            learnt = keep

        for v in to_clear:
            self.seen[v] = False

        if len(learnt) == 1:
            bt = 0
        else:
            mi = max(range(1, len(learnt)), key=lambda k: self.level[learnt[k] >> 1])
            learnt[1], learnt[mi] = learnt[mi], learnt[1]
            bt = self.level[learnt[1] >> 1]
        lbd = len({self.level[x >> 1] for x in learnt})
        self.var_inc /= self.opt.var_decay
        return learnt, bt, lbd

    # ------------------------------------------------------- heuristics
    def _pick_branch(self) -> Optional[int]:
        v: Optional[int] = None
        if self.opt.branching == "ordered":
            v = next((u for u in range(1, self.n + 1) if self.value[u] == UNDEF), None)
        elif self.opt.branching == "random":
            free = [u for u in range(1, self.n + 1) if self.value[u] == UNDEF]
            v = self.rng.choice(free) if free else None
        else:
            while self.heap:
                neg_act, u = heapq.heappop(self.heap)
                if self.value[u] == UNDEF and -neg_act == self.activity[u]:
                    v = u
                    break
            if v is None:   # heap entries can go stale; fall back to a scan
                free = [u for u in range(1, self.n + 1) if self.value[u] == UNDEF]
                v = max(free, key=lambda u: self.activity[u]) if free else None
        if v is None:
            return None
        positive = self.saved_phase[v] if self.opt.phase_saving else False
        return 2 * v + (0 if positive else 1)

    def _reduce_db(self) -> None:
        locked = {id(self.reason[x >> 1]) for x in self.trail if self.reason[x >> 1] is not None}
        cands = sorted((c for c in self.learnts if c.lbd > 2 and id(c) not in locked),
                       key=lambda c: (c.lbd, len(c.lits)), reverse=True)
        remove = cands[: len(cands) // 2]
        for c in remove:
            c.deleted = True
            if self.opt.proof:
                self.proof.append(("d", [_dec(x) for x in c.lits]))
        removed = {id(c) for c in remove}
        self.learnts = [c for c in self.learnts if id(c) not in removed]
        self.stats.deleted += len(remove)
        self.trace.emit("reduce", removed=len(remove), kept=len(self.learnts))

    def _should_restart(self, conflicts_since: int, restart_idx: int) -> bool:
        if self.opt.restarts == "luby":
            return conflicts_since >= self.opt.luby_unit * luby(restart_idx)
        if self.opt.restarts == "glucose":
            if len(self.lbd_recent) < self.lbd_recent.maxlen or self.lbd_count == 0:
                return False
            recent = sum(self.lbd_recent) / len(self.lbd_recent)
            return recent * 0.8 > self.lbd_sum / self.lbd_count
        return False

    # --------------------------------------------------------------- solve
    def solve(self, assumptions: Sequence[int] = (),
              max_conflicts: Optional[int] = None) -> Result:
        if not self.ok:
            if self.opt.proof and ("a", []) not in self.proof:
                self.proof.append(("a", []))
            self.trace.emit("result", sat=False)
            return Result(False, stats=self.stats)
        self.ensure_vars(max((abs(a) for a in assumptions), default=0))
        assume = [_enc(a) for a in assumptions]
        self._cancel_until(0)
        if self._propagate() is not None:
            self.ok = False
            if self.opt.proof:
                self.proof.append(("a", []))
            self.trace.emit("result", sat=False)
            return Result(False, stats=self.stats)
        if self.max_learnts == 0:
            self.max_learnts = max(len(self.clauses) / 3, 100)

        conflicts_at_start = self.stats.conflicts
        conflicts_since_restart = 0
        restart_idx = 0
        while True:
            confl = self._propagate()
            if confl is not None:
                self.stats.conflicts += 1
                conflicts_since_restart += 1
                if self.trace.enabled:
                    self.trace.emit("conflict", clause=[_dec(x) for x in confl.lits],
                                    level=self.decision_level())
                if self.decision_level() == 0:
                    self.ok = False
                    if self.opt.proof:
                        self.proof.append(("a", []))
                    self.trace.emit("result", sat=False)
                    return Result(False, stats=self.stats)
                learnt, bt, lbd = self._analyze(confl)
                self._cancel_until(bt)
                self.stats.learned += 1
                self.stats.learned_literals += len(learnt)
                self.lbd_recent.append(lbd)
                self.lbd_sum += lbd
                self.lbd_count += 1
                if self.opt.proof:
                    self.proof.append(("a", [_dec(x) for x in learnt]))
                if self.trace.enabled:
                    self.trace.emit("learn", clause=[_dec(x) for x in learnt],
                                    uip=_dec(learnt[0]), lbd=lbd, backjump=bt)
                    self.trace.emit("backjump", to=bt)
                if len(learnt) == 1:
                    self._enqueue(learnt[0], None)
                else:
                    c = _Clause(learnt, learnt=True, lbd=lbd)
                    self.learnts.append(c)
                    self._attach(c)
                    self._enqueue(learnt[0], c)
                continue

            # no conflict
            if (max_conflicts is not None
                    and self.stats.conflicts - conflicts_at_start >= max_conflicts):
                self._cancel_until(0)
                self.trace.emit("result", sat=None)
                return Result(None, stats=self.stats)
            if self._should_restart(conflicts_since_restart, restart_idx):
                self.stats.restarts += 1
                self.trace.emit("restart", conflicts=self.stats.conflicts)
                restart_idx += 1
                conflicts_since_restart = 0
                self.lbd_recent.clear()
                self._cancel_until(0)
                continue
            if self.opt.reduce and len(self.learnts) - len(self.trail) >= self.max_learnts:
                self._reduce_db()
                self.max_learnts *= 1.1

            # assumptions are decided first, one decision level each
            nxt: Optional[int] = None
            while self.decision_level() < len(assume):
                a = assume[self.decision_level()]
                va = self._val(a)
                if va == TRUE:
                    self.trail_lim.append(len(self.trail))   # dummy level
                elif va == FALSE:
                    failed = self._failed_assumptions(a ^ 1, set(assume))
                    self._cancel_until(0)
                    self.trace.emit("result", sat=False)
                    return Result(False, stats=self.stats, failed_assumptions=failed)
                else:
                    nxt = a
                    break
            if nxt is None:
                nxt = self._pick_branch()
                if nxt is None:
                    model = {v: self.value[v] == TRUE for v in range(1, self.n + 1)}
                    self._cancel_until(0)
                    self.trace.emit("result", sat=True)
                    return Result(True, model, self.stats)
                self.stats.decisions += 1
            self.trail_lim.append(len(self.trail))
            self.stats.max_level = max(self.stats.max_level, self.decision_level())
            self._enqueue(nxt, None)
            if self.trace.enabled:
                self.trace.emit("decide", lit=_dec(nxt), level=self.decision_level())

    def _failed_assumptions(self, false_lit: int, assume: set) -> List[int]:
        """Which assumptions (DIMACS) imply ``false_lit`` (the negation of one)."""
        out = {_dec(false_lit ^ 1)}
        stack = [false_lit >> 1]
        visited = set()
        while stack:
            v = stack.pop()
            if v in visited:
                continue
            visited.add(v)
            r = self.reason[v]
            if r is None:
                if self.level[v] > 0:
                    lit = 2 * v + (0 if self.value[v] == TRUE else 1)
                    if lit in assume:
                        out.add(_dec(lit))
            else:
                stack.extend(x >> 1 for x in r.lits if (x >> 1) != v)
        return sorted(out, key=abs)

    def drup(self) -> str:
        lines = []
        for kind, lits in self.proof:
            prefix = "d " if kind == "d" else ""
            lines.append(prefix + " ".join(map(str, lits + [0])))
        return "\n".join(lines) + ("\n" if lines else "")


def solve(cnf: CNF, options: Optional[Options] = None, trace: Optional[Trace] = None,
          max_conflicts: Optional[int] = None) -> Result:
    return Solver(cnf, options, trace).solve(max_conflicts=max_conflicts)
