"""Emit a Lean 4 model from the sv2lean IR.

Semantics of each Yosys cell follow the Yosys manual ("Internal cell library"):
operands are extended to the relevant width (sign-extended only if *both*
operands are signed), arithmetic wraps, comparisons produce one bit that is
zero-extended to Y_WIDTH. Every intermediate gets an explicit `BitVec n` type.
"""

from __future__ import annotations

from typing import Dict, List, Optional, Sequence, Tuple

from .ir import Bit, CombCell, Design, FormalProp, Signal, UnsupportedDesign


class Ctx:
    """How to refer to each kind of signal at the current emission site."""

    def __init__(self, comb_prefix: str):
        self.comb_prefix = comb_prefix

    def ref(self, sig: Signal) -> str:
        if sig.kind == "input":
            return f"i.{sig.name}"
        if sig.kind == "reg":
            return f"s.{sig.name}"
        return f"{self.comb_prefix}{sig.name}"


def bits_expr(d: Design, bits: Sequence[Bit], ctx: Ctx) -> str:
    """Word-level Lean expression (width len(bits)) for a list of net bits, LSB first."""
    w = len(bits)
    if w == 0:
        raise UnsupportedDesign("zero-width signal")
    chunks: List[Tuple[str, int]] = []         # (expr, width), LSB chunk first
    i = 0
    while i < w:
        b = bits[i]
        if isinstance(b, str):
            j = i
            while j < w and isinstance(bits[j], str):
                j += 1
            const = bits[i:j]
            if any(c not in "01" for c in const):
                d.warnings.append("x/z constant bits treated as 0")
            val = sum(1 << k for k, c in enumerate(const) if c == "1")
            chunks.append((f"{val}#{j - i}", j - i))
            i = j
            continue
        sig, idx = d.driver[b]
        j = i + 1
        while (j < w and isinstance(bits[j], int) and d.driver[bits[j]][0] is sig
               and d.driver[bits[j]][1] == idx + (j - i)):
            j += 1
        n = j - i
        ref = ctx.ref(sig)
        if idx == 0 and n == sig.width:
            chunks.append((ref, n))
        else:
            chunks.append((f"({ref}.extractLsb {idx + n - 1} {idx})", n))
        i = j
    if len(chunks) == 1:
        e, cw = chunks[0]
        return e if cw == w and not e.startswith("(") else f"({e} : BitVec {w})"
    return "(" + " ++ ".join(e for e, _ in reversed(chunks)) + f" : BitVec {w})"


def ext(e: str, frm: int, to: int, signed: bool) -> str:
    if frm == to:
        return e
    return f"(({e}).signExtend {to})" if signed else f"(({e}).setWidth {to})"


def cell_expr(d: Design, c: CombCell, ctx: Ctx) -> str:
    t, p, cn = c.type, c.params, c.conns
    yw = c.sig.width

    def port(name: str) -> str:
        return bits_expr(d, cn[name], ctx)

    if t in ("$mux",):
        return f"(if {port('S')} = 1#1 then {port('B')} else {port('A')})"
    if t == "$pmux":
        # Several active selects (e.g. a violated `unique case`) are undefined in the Yosys
        # manual. Yosys's formal backends (sat, smt2, hence SymbiYosys) let the LAST active
        # select win, so the model does the same and agrees with them on every input.
        w, n = p["WIDTH"], p["S_WIDTH"]
        s = port("S")
        b = cn["B"]
        out = port("A")
        for k in range(n):
            bk = bits_expr(d, b[k * w:(k + 1) * w], ctx)
            out = f"(if ({s}).getLsbD {k} then {bk} else {out})"
        return out

    aw = p.get("A_WIDTH", len(cn.get("A", [])))
    asg = bool(p.get("A_SIGNED", 0))
    a = port("A")
    if "B" in cn:
        bw = p.get("B_WIDTH", len(cn["B"]))
        bsg = bool(p.get("B_SIGNED", 0))
        b = port("B")
        both = asg and bsg

    if t in ("$add", "$sub", "$mul", "$and", "$or", "$xor", "$xnor"):
        op = {"$add": "+", "$sub": "-", "$mul": "*", "$and": "&&&", "$or": "|||",
              "$xor": "^^^", "$xnor": "^^^"}[t]
        e = f"({ext(a, aw, yw, both)} {op} {ext(b, bw, yw, both)})"
        return f"(~~~{e})" if t == "$xnor" else e
    if t == "$not":
        return f"(~~~{ext(a, aw, yw, asg)})"
    if t == "$neg":
        return f"(-{ext(a, aw, yw, asg)})"
    if t == "$pos":
        return ext(a, aw, yw, asg)

    if t in ("$eq", "$ne", "$eqx", "$nex", "$lt", "$le", "$gt", "$ge"):
        mw = max(aw, bw)
        x, y = ext(a, aw, mw, both), ext(b, bw, mw, both)
        if t in ("$eq", "$eqx"):
            r = f"({x} == {y})"
        elif t in ("$ne", "$nex"):
            r = f"({x} != {y})"
        else:
            lt, le = (".slt", ".sle") if both else (".ult", ".ule")
            r = {"$lt": f"(({x}){lt} {y})", "$le": f"(({x}){le} {y})",
                 "$gt": f"(({y}){lt} {x})", "$ge": f"(({y}){le} {x})"}[t]
        return ext(f"BitVec.ofBool {r}", 1, yw, False)

    if t == "$logic_not":
        return ext(f"BitVec.ofBool ({a} == 0#{aw})", 1, yw, False)
    if t in ("$logic_and", "$logic_or"):
        op = "&&" if t == "$logic_and" else "||"
        return ext(f"BitVec.ofBool (({a} != 0#{aw}) {op} ({b} != 0#{bw}))", 1, yw, False)
    if t == "$reduce_and":
        return ext(f"BitVec.ofBool ({a} == BitVec.allOnes {aw})", 1, yw, False)
    if t in ("$reduce_or", "$reduce_bool"):
        return ext(f"BitVec.ofBool ({a} != 0#{aw})", 1, yw, False)
    if t in ("$reduce_xor", "$reduce_xnor"):
        par = " ^^ ".join(f"({a}).getLsbD {k}" for k in range(aw))
        if t == "$reduce_xnor":
            par = f"!({par})"
        return ext(f"BitVec.ofBool ({par})", 1, yw, False)

    if t in ("$shl", "$sshl", "$shr", "$sshr"):
        if bsg:
            raise UnsupportedDesign(f"signed shift amount in {c.src}")
        if t in ("$shl", "$sshl"):
            return f"({ext(a, aw, yw, asg)} <<< {b})"
        mw = max(aw, yw)
        wide = ext(a, aw, mw, asg)
        r = f"(BitVec.sshiftRight' {wide} {b})" if (t == "$sshr" and asg) else f"({wide} >>> {b})"
        return ext(r, mw, yw, False)

    raise UnsupportedDesign(f"no Lean semantics for {t} ({c.src})")


def _prop_body(d: Design, p: FormalProp, ctx: Ctx) -> str:
    a, en = bits_expr(d, p.a, ctx), bits_expr(d, p.en, ctx)
    if p.kind == "cover":
        return f"{en} = 1#1 ∧ {a} = 1#1"
    return f"{en} = 1#1 → {a} = 1#1"


def emit(d: Design, namespace: str, source_note: str = "") -> str:
    L: List[str] = []
    add = L.append
    add("import RtlProof.Core.Circuit")
    add("")
    add("/-!")
    add(f"# Generated model of `{d.top}`")
    add("")
    add(f"Generated by `sv2lean`{(' from ' + source_note) if source_note else ''}. **Do not edit.**")
    add("Regenerate with `python -m sv2lean ...`; see tools/sv2lean.")
    add("")
    add("* `State`: one field per register; `Input`: one field per input port (clock removed).")
    add("* `comb s i`: every combinational signal; `step s i`: the next state (one clock edge).")
    add("* `initOK s`: the `initial`/`init` constraints; `init0`: those values, other bits 0.")
    add("* `assumptions s i`: conjunction of all `assume`s (prefix semantics in `SafePrefix`).")
    add("* One `Prop` per `assert` (`en = 1 → a = 1`) and per `cover` (`en = 1 ∧ a = 1`).")
    add("-/")
    add("")
    add(f"namespace {namespace}")
    add("open RtlProof")
    add("set_option linter.unusedVariables false  -- combinational designs ignore `s`, etc.")
    add("")

    def struct(name: str, doc: str, sigs: Sequence[Signal], derive: str) -> None:
        add(f"/-- {doc} -/")
        add(f"structure {name} where")
        if not sigs:
            add("  dummy : Unit := ()")
        for s in sigs:
            add(f"  {s.name} : BitVec {s.width}")
        add(f"deriving {derive}")
        add("")

    undef_note = (" Fields `undef_k` stand for constant `x` bits in the RTL: values the hardware "
                  "does not promise, so proofs must hold for every value of them."
                  if any(s.undef for s in d.inputs) else "")
    struct("Input", f"Inputs of `{d.top}`" + (f" (clock `{d.clock}` removed)." if d.clock else ".")
           + undef_note, d.inputs, "Repr, DecidableEq, Inhabited")
    struct("State", f"Registers of `{d.top}`.", [r.sig for r in d.regs], "Repr, DecidableEq, Inhabited")
    struct("Comb", "Combinational signals.", [c.sig for c in d.comb], "Repr")

    inner = Ctx("")
    add("set_option maxRecDepth 16384 in")
    add("/-- All combinational logic, in dependency order. -/")
    add("def comb (s : State) (i : Input) : Comb :=")
    for c in d.comb:
        add(f"  -- {c.type} {c.src}")
        add(f"  let {c.sig.name} : BitVec {c.sig.width} := {cell_expr(d, c, inner)}")
    if d.comb:
        # positional constructor: a `{ a, b, … }` literal with hundreds of fields is slow to elaborate
        add("  Comb.mk " + " ".join(c.sig.name for c in d.comb))
    else:
        add("  {}")
    add("")

    outer = Ctx("w.")
    if d.outputs:
        from .ir import _ident
        oused: set = set()
        onames = [(_ident(n, oused), n, bits) for n, bits in d.outputs]
        add("/-- The module's output ports (some are plain wires, not combinational cells). -/")
        add("structure Outputs where")
        for ln, _, bits in onames:
            add(f"  {ln} : BitVec {len(bits)}")
        add("deriving Repr")
        add("")
        add("/-- Output ports, given the current state and inputs. -/")
        add("def outputs (s : State) (i : Input) : Outputs :=")
        add("  let w := comb s i")
        add("  Outputs.mk " + " ".join(f"({bits_expr(d, bits, outer)})" for _, _, bits in onames))
        add("")
    add("/-- One clock edge. -/")
    add("def step (s : State) (i : Input) : State :=")
    add("  let w := comb s i")
    if d.regs:
        fields = []
        for r in d.regs:
            rhs = f"s.{r.sig.name}" if r.free else bits_expr(d, r.d, outer)
            fields.append(f"{r.sig.name} := {rhs}")
        add("  { " + ",\n    ".join(fields) + " }")
    else:
        add("  {}")
    add("")

    conds = []
    for r in d.regs:
        if all(v is None for v in r.init):
            continue
        if all(v is not None for v in r.init):
            val = sum(v << k for k, v in enumerate(r.init))
            conds.append(f"s.{r.sig.name} = {val}#{r.sig.width}")
        else:
            for k, v in enumerate(r.init):
                if v is not None:
                    conds.append(f"s.{r.sig.name}.getLsbD {k} = {'true' if v else 'false'}")
    add("/-- Initial-value constraints from `initial` blocks / `init` attributes. -/")
    add("def initOK (s : State) : Prop := " + (" ∧ ".join(conds) if conds else "True"))
    add("")
    add("/-- A concrete initial state: `init` values where given, 0 elsewhere. -/")
    if d.regs:
        vals = []
        for r in d.regs:
            v = sum((b or 0) << k for k, b in enumerate(r.init))
            vals.append(f"{r.sig.name} := {v}#{r.sig.width}")
        add("def init0 : State := { " + ", ".join(vals) + " }")
    else:
        add("def init0 : State := {}")
    add("")

    assumes = [p for p in d.props if p.kind == "assume"]
    add("/-- All `assume`s, as one predicate on the current state and inputs. -/")
    if assumes:
        add("def assumptions (s : State) (i : Input) : Prop :=")
        add("  let w := comb s i")
        add("  " + " ∧\n  ".join(f"({_prop_body(d, p, outer)})" for p in assumes))
    else:
        add("def assumptions (_s : State) (_i : Input) : Prop := True")
    add("")

    for p in d.props:
        if p.kind == "assume":
            continue
        what = "Assertion" if p.kind == "assert" else "Cover target"
        add(f"/-- {what} `{p.name}` ({p.src}). -/")
        add(f"def {p.name} (s : State) (i : Input) : Prop :=")
        add("  let w := comb s i")
        add(f"  {_prop_body(d, p, outer)}")
        add("")

    add("/-- The design as a `Circuit`, started from state `s0`. -/")
    add("def circuit (s0 : State) : Circuit Input State := ⟨s0, step⟩")
    add("")
    add(f"end {namespace}")
    return "\n".join(L) + "\n"
