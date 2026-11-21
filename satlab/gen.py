"""Instance generators for the SAT lab.

Each generator returns a ``CNF`` (with variable names where meaningful).
The hardware-flavoured ones mirror course designs so the same circuit shows up
in the SAT lab, the model checker, and Lean:

* ``add_comm_miter(w)``  — is x+y ≡ y+x? (UNSAT = equivalent). Easy for SAT.
* ``mul_comm_miter(w)``  — is x*y ≡ y*x? Famously hard for SAT as w grows,
  trivial in Lean by algebra (course D6).
* ``counter_bmc(k)``     — bounded model check of the BCD counter from
  LEAN_FLUENCY L14: can ``cnt > 9`` happen within k cycles? (UNSAT = no.)
  ``wrap=10`` injects the off-by-one bug; the model is then a counterexample.
* ``pigeonhole(n)``      — n+1 pigeons, n holes: UNSAT, exponentially hard for
  resolution-based solvers (and so for CDCL).
* ``random_ksat(n, m)``  — uniform random k-SAT; m/n ≈ 4.26 is the hard region
  for k = 3.
"""

from __future__ import annotations

import random
from dataclasses import dataclass, field
from typing import Dict, List

from .cnf import BV, CNF, bv_value, model_value


def pigeonhole(n: int) -> CNF:
    cnf = CNF()
    p = [[cnf.new_var(f"p{i}h{j}") for j in range(n)] for i in range(n + 1)]
    for i in range(n + 1):
        cnf.add(p[i])                                  # every pigeon has a hole
    for j in range(n):
        for a in range(n + 1):
            for b in range(a + 1, n + 1):
                cnf.add([-p[a][j], -p[b][j]])          # no hole holds two
    return cnf


def random_ksat(n: int, m: int, k: int = 3, seed: int = 0) -> CNF:
    rng = random.Random(seed)
    cnf = CNF(num_vars=n)
    for _ in range(m):
        vs = rng.sample(range(1, n + 1), k)
        cnf.add([v if rng.random() < 0.5 else -v for v in vs])
    return cnf


def _miter(cnf: CNF, a: BV, b: BV) -> None:
    cnf.add([-cnf.bv_eq(a, b)])        # assert the outputs differ somewhere


def add_comm_miter(width: int) -> CNF:
    cnf = CNF()
    x, y = cnf.new_bv(width, "x"), cnf.new_bv(width, "y")
    _miter(cnf, cnf.bv_add(x, y), cnf.bv_add(y, x))
    return cnf


def mul_comm_miter(width: int) -> CNF:
    cnf = CNF()
    x, y = cnf.new_bv(width, "x"), cnf.new_bv(width, "y")
    _miter(cnf, cnf.bv_mul(x, y), cnf.bv_mul(y, x))
    return cnf


@dataclass
class BMCInstance:
    cnf: CNF
    cnt: List[BV] = field(default_factory=list)   # cnt at frames 0..k
    en: List[int] = field(default_factory=list)   # en at frames 0..k-1

    def decode(self, model: Dict[int, bool]) -> List[Dict[str, int]]:
        """Turn a satisfying assignment into a per-cycle trace (a CEX)."""
        rows = []
        for i, c in enumerate(self.cnt):
            row = {"cycle": i, "cnt": bv_value(model, c)}
            if i < len(self.en):
                row["en"] = int(model_value(model, self.en[i]))
            rows.append(row)
        return rows


def counter_bmc(k: int, wrap: int = 9, bound: int = 9) -> BMCInstance:
    """Unroll the 4-bit BCD counter k cycles; assert cnt > bound at some frame.

    RTL: if (en) cnt <= (cnt == WRAP) ? 0 : cnt + 1;   reset value 0.
    """
    cnf = CNF()
    inst = BMCInstance(cnf)
    cnt = cnf.const(0, 4)
    inst.cnt.append(cnt)
    for i in range(k):
        en = cnf.new_var(f"en@{i}")
        inst.en.append(en)
        at_wrap = cnf.bv_eq(cnt, cnf.const(wrap, 4))
        inc = cnf.bv_add(cnt, cnf.const(1, 4))
        advanced = cnf.bv_ite(at_wrap, cnf.const(0, 4), inc)
        nxt = cnf.bv_ite(en, advanced, cnt)
        for b, lit in enumerate(nxt):
            v = cnf.new_var(f"cnt@{i + 1}[{b}]")
            cnf.add([-v, lit])
            cnf.add([v, -lit])
            nxt[b] = v
        cnt = nxt
        inst.cnt.append(cnt)
    bad = [cnf.bv_ult(cnf.const(bound, 4), c) for c in inst.cnt]
    cnf.add([cnf.OR_N(bad)])
    return inst
