"""CNF formulas, DIMACS I/O, and Tseitin encoders for gates and bit-vectors.

Literals use the DIMACS convention throughout the public API: variable ``v``
is the positive integer ``v``, its negation is ``-v``.

Bit-vectors are Python lists of literals, least-significant bit first, so
``bv[0]`` is bit 0 — the same convention as ``BitVec.getLsbD`` in Lean.
Arithmetic wraps modulo 2**width, exactly like RTL and Lean's ``BitVec``.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, Iterable, List, Optional, Sequence, TextIO

Clause = List[int]
BV = List[int]


@dataclass
class CNF:
    num_vars: int = 0
    clauses: List[Clause] = field(default_factory=list)
    names: Dict[int, str] = field(default_factory=dict)
    _true: Optional[int] = None

    # ------------------------------------------------------------------ basics
    def new_var(self, name: Optional[str] = None) -> int:
        self.num_vars += 1
        if name is not None:
            self.names[self.num_vars] = name
        return self.num_vars

    def new_bv(self, width: int, name: Optional[str] = None) -> BV:
        return [self.new_var(f"{name}[{i}]" if name else None) for i in range(width)]

    def add(self, clause: Iterable[int]) -> None:
        c = list(clause)
        for lit in c:
            if lit == 0 or abs(lit) > self.num_vars:
                raise ValueError(f"literal {lit} out of range (num_vars={self.num_vars})")
        self.clauses.append(c)

    def true(self) -> int:
        """A literal constrained to be true (created on first use)."""
        if self._true is None:
            self._true = self.new_var("TRUE")
            self.add([self._true])
        return self._true

    def false(self) -> int:
        return -self.true()

    def const(self, value: int, width: int) -> BV:
        return [self.true() if (value >> i) & 1 else self.false() for i in range(width)]

    def copy(self) -> "CNF":
        return CNF(self.num_vars, [list(c) for c in self.clauses], dict(self.names), self._true)

    # ------------------------------------------------------------ evaluation
    def satisfied_by(self, model: Dict[int, bool]) -> bool:
        def val(lit: int) -> bool:
            v = model.get(abs(lit), False)
            return v if lit > 0 else not v

        return all(any(val(l) for l in c) for c in self.clauses)

    # ------------------------------------------------------------------ DIMACS
    def to_dimacs(self, comments: Sequence[str] = ()) -> str:
        lines = [f"c {c}" for c in comments]
        for v, n in sorted(self.names.items()):
            lines.append(f"c var {v} {n}")
        lines.append(f"p cnf {self.num_vars} {len(self.clauses)}")
        lines.extend(" ".join(map(str, c)) + " 0" for c in self.clauses)
        return "\n".join(lines) + "\n"

    def write(self, fp: TextIO, comments: Sequence[str] = ()) -> None:
        fp.write(self.to_dimacs(comments))

    @staticmethod
    def from_dimacs(text: str) -> "CNF":
        cnf = CNF()
        declared = None
        pending: Clause = []
        for raw in text.splitlines():
            line = raw.strip()
            if not line or line.startswith("%"):
                continue
            if line.startswith("c"):
                parts = line.split()
                if len(parts) >= 4 and parts[1] == "var":
                    cnf.names[int(parts[2])] = " ".join(parts[3:])
                continue
            if line.startswith("p"):
                parts = line.split()
                if len(parts) != 4 or parts[1] != "cnf":
                    raise ValueError(f"bad problem line: {line!r}")
                declared = int(parts[2])
                cnf.num_vars = declared
                continue
            for tok in line.split():
                lit = int(tok)
                if lit == 0:
                    cnf.clauses.append(pending)
                    pending = []
                else:
                    cnf.num_vars = max(cnf.num_vars, abs(lit))
                    pending.append(lit)
        if pending:
            cnf.clauses.append(pending)
        return cnf

    # ----------------------------------------------------- Tseitin: gates
    def AND(self, a: int, b: int) -> int:
        c = self.new_var()
        self.add([-c, a])
        self.add([-c, b])
        self.add([c, -a, -b])
        return c

    def OR(self, a: int, b: int) -> int:
        return -self.AND(-a, -b)

    def XOR(self, a: int, b: int) -> int:
        c = self.new_var()
        self.add([-c, a, b])
        self.add([-c, -a, -b])
        self.add([c, -a, b])
        self.add([c, a, -b])
        return c

    def MUX(self, sel: int, a: int, b: int) -> int:
        """sel ? a : b"""
        c = self.new_var()
        self.add([-sel, -a, c])
        self.add([-sel, a, -c])
        self.add([sel, -b, c])
        self.add([sel, b, -c])
        return c

    def AND_N(self, lits: Sequence[int]) -> int:
        if not lits:
            return self.true()
        c = self.new_var()
        for l in lits:
            self.add([-c, l])
        self.add([c] + [-l for l in lits])
        return c

    def OR_N(self, lits: Sequence[int]) -> int:
        return -self.AND_N([-l for l in lits])

    def full_adder(self, a: int, b: int, cin: int) -> tuple[int, int]:
        s = self.XOR(self.XOR(a, b), cin)
        cout = self.OR(self.AND(a, b), self.AND(cin, self.XOR(a, b)))
        return s, cout

    # ----------------------------------------------- Tseitin: bit-vectors
    def bv_add(self, x: BV, y: BV) -> BV:
        """Ripple-carry adder, wrapping (carry-out dropped)."""
        assert len(x) == len(y)
        out, carry = [], self.false()
        for a, b in zip(x, y):
            s, carry = self.full_adder(a, b, carry)
            out.append(s)
        return out

    def bv_mul(self, x: BV, y: BV) -> BV:
        """Shift-and-add array multiplier, wrapping to len(x) bits."""
        w = len(x)
        assert len(y) == w
        acc = self.const(0, w)
        for i in range(w):
            partial = [self.false()] * i + [self.AND(x[j], y[i]) for j in range(w - i)]
            acc = self.bv_add(acc, partial)
        return acc

    def bv_eq(self, x: BV, y: BV) -> int:
        return self.AND_N([-self.XOR(a, b) for a, b in zip(x, y)])

    def bv_ult(self, x: BV, y: BV) -> int:
        """Unsigned x < y, scanning from the LSB up (MSB decides last)."""
        lt = self.false()
        for a, b in zip(x, y):
            # at this bit: x<y if (¬a ∧ b) or (a == b ∧ lower bits say x<y)
            eq = -self.XOR(a, b)
            lt = self.OR(self.AND(-a, b), self.AND(eq, lt))
        return lt

    def bv_ite(self, sel: int, x: BV, y: BV) -> BV:
        return [self.MUX(sel, a, b) for a, b in zip(x, y)]


def model_value(model: Dict[int, bool], lit: int) -> bool:
    v = model.get(abs(lit), False)
    return v if lit > 0 else not v


def bv_value(model: Dict[int, bool], bv: BV) -> int:
    return sum(1 << i for i, l in enumerate(bv) if model_value(model, l))
