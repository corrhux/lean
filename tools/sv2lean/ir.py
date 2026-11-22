"""Typed intermediate representation built from a Yosys JSON module.

Assumes the netlist was lowered by `frontend.lower_script`: flat, every
flip-flop a plain `$dff` on one clock, processes already converted to cells.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple, Union

Bit = Union[int, str]          # net id, or constant "0" / "1" / "x" / "z"

LEAN_KEYWORDS = {
    "at", "by", "def", "do", "else", "end", "example", "fun", "have", "if", "import",
    "in", "instance", "let", "match", "namespace", "open", "section", "show", "structure",
    "then", "theorem", "where", "with", "from", "for", "mut", "return", "unless", "class",
    "abbrev", "inductive", "variable", "universe", "deriving", "calc", "true", "false",
    "Type", "Prop", "Sort", "mk", "comb", "step", "init0", "initOK", "assumptions",
    "circuit", "s", "i", "w",
}

COMB_TYPES = {
    "$add", "$sub", "$mul", "$and", "$or", "$xor", "$xnor", "$not", "$neg", "$pos",
    "$eq", "$ne", "$eqx", "$nex", "$lt", "$le", "$gt", "$ge",
    "$logic_not", "$logic_and", "$logic_or",
    "$reduce_and", "$reduce_or", "$reduce_bool", "$reduce_xor", "$reduce_xnor",
    "$shl", "$shr", "$sshl", "$sshr", "$shiftx", "$mux", "$pmux",
}
FORMAL_TYPES = {"$assert", "$assume", "$cover"}


class UnsupportedDesign(Exception):
    pass


@dataclass
class Signal:
    name: str                  # Lean identifier
    width: int
    kind: str                  # "input" | "reg" | "comb"
    yosys_name: Optional[str] = None
    undef: bool = False        # stands for constant x/z bits in the RTL (an unconstrained value)


@dataclass
class Reg:
    sig: Signal
    d: List[Bit]
    q: List[int]
    init: List[Optional[int]]  # per bit, LSB first; None = unconstrained
    free: bool = False         # $anyconst: arbitrary initial value, never changes


@dataclass
class CombCell:
    sig: Signal
    type: str
    params: Dict[str, int]
    conns: Dict[str, List[Bit]]
    src: str


@dataclass
class FormalProp:
    name: str
    kind: str                  # "assert" | "assume" | "cover"
    a: List[Bit]
    en: List[Bit]
    src: str


@dataclass
class Design:
    top: str
    inputs: List[Signal] = field(default_factory=list)
    regs: List[Reg] = field(default_factory=list)
    comb: List[CombCell] = field(default_factory=list)          # topologically sorted
    props: List[FormalProp] = field(default_factory=list)
    driver: Dict[int, Tuple[Signal, int]] = field(default_factory=dict)
    clock: Optional[str] = None
    warnings: List[str] = field(default_factory=list)
    outputs: List[Tuple[str, List[Bit]]] = field(default_factory=list)   # (port name, bits)


_REPO = __import__("pathlib").Path(__file__).resolve().parents[2].as_posix() + "/"


def _relsrc(src: str) -> str:
    """Source locations relative to the repository, so regenerated files are identical."""
    src = src.replace(_REPO, "")
    # sv2v output lives in a fresh temp dir; name it stably so regenerated files are identical
    return re.sub(r"build/tmp/tmp[^/|]+/", "sv2v/", src)


def _int(v: Union[str, int]) -> int:
    if isinstance(v, int):
        return v
    v = v.strip()
    if v and set(v) <= {"0", "1"}:
        return int(v, 2)
    return int(v)


def _ident(raw: str, used: set) -> str:
    base = raw.lstrip("\\$")
    base = re.sub(r"[^A-Za-z0-9_]", "_", base)
    base = re.sub(r"_+", "_", base).strip("_") or "sig"
    if base[0].isdigit():
        base = "n" + base
    if base in LEAN_KEYWORDS:
        base += "_"
    name, k = base, 1
    while name in used:
        k += 1
        name = f"{base}_{k}"
    used.add(name)
    return name


def build(module: dict, top: str) -> Design:
    d = Design(top)
    cells = module.get("cells", {})
    netnames = module.get("netnames", {})
    used: set = set()

    def exact_name(bits: List[int], prefer_visible: bool = True) -> Optional[str]:
        best = None
        for n, info in netnames.items():
            if info["bits"] == bits:
                if not info.get("hide_name", 0) and not n.startswith("$"):
                    return n
                best = best or n
        return None if prefer_visible else best

    # ---- initial values (per bit)
    init_of: Dict[int, int] = {}
    for info in netnames.values():
        iv = info.get("attributes", {}).get("init")
        if iv is None:
            continue
        s = iv if isinstance(iv, str) else format(iv, "b")
        s = s.rjust(len(info["bits"]), "0")
        for bit, ch in zip(info["bits"], reversed(s)):
            if isinstance(bit, int) and ch in "01":
                init_of[bit] = int(ch)

    # ---- x/z constants become unconstrained inputs. A proof then has to hold whatever
    # value the hardware picks, which is how Yosys's formal backends treat x as well.
    # (Treating x as 0 would let a proof depend on a value the RTL does not promise.)
    next_id = 1 + max([b for c in cells.values() for bits in c["connections"].values()
                       for b in bits if isinstance(b, int)] + [0])
    cells = {n: dict(c, connections={k: list(v) for k, v in c["connections"].items()})
             for n, c in cells.items()}
    for cname in sorted(cells):
        for port, bits in cells[cname]["connections"].items():
            i = 0
            while i < len(bits):
                if bits[i] in ("x", "z"):
                    j = i
                    while j < len(bits) and bits[j] in ("x", "z"):
                        j += 1
                    sig = Signal(_ident(f"undef_{len([s for s in d.inputs if s.undef])}", used),
                                 j - i, "input", None, undef=True)
                    d.inputs.append(sig)
                    for k in range(i, j):
                        bits[k] = next_id
                        d.driver[next_id] = (sig, k - i)
                        next_id += 1
                    i = j
                else:
                    i += 1

    # ---- clock
    clk_bits = set()
    for c in cells.values():
        if c["type"] == "$dff":
            clk_bits.update(b for b in c["connections"]["CLK"] if isinstance(b, int))
        elif c["type"] in ("$adff", "$sdff", "$dffe", "$sdffe", "$adffe", "$dffsr", "$aldff",
                           "$dlatch", "$sr", "$ff"):
            raise UnsupportedDesign(f"flip-flop type {c['type']} survived lowering")
    if len(clk_bits) > 1:
        raise UnsupportedDesign("more than one clock: only single-clock designs are supported")

    # ---- inputs
    for pname, p in module.get("ports", {}).items():
        if p["direction"] == "inout":
            raise UnsupportedDesign(f"inout port {pname}")
        if p["direction"] == "output":
            d.outputs.append((pname, list(p["bits"])))
            continue
        if p["direction"] != "input":
            continue
        if set(p["bits"]) & clk_bits:
            if len(p["bits"]) != 1:
                raise UnsupportedDesign(f"clock {pname} is a vector")
            d.clock = pname
            continue
        sig = Signal(_ident(pname, used), len(p["bits"]), "input", pname)
        d.inputs.append(sig)
        for k, b in enumerate(p["bits"]):
            d.driver[b] = (sig, k)

    # A flop with an asynchronous reset is lowered (async2sync) to a plain flop followed by
    # a reset mux, and the RTL's name (e.g. `md_state_q`) lands on the mux output. Name such
    # a flop after it: `md_state_q_ff`.
    reset_mux_name: Dict[Tuple[int, ...], str] = {}
    for c in cells.values():
        if c["type"] == "$mux":
            out = exact_name(c["connections"]["Y"])
            if out:
                for side in ("A", "B"):
                    reset_mux_name.setdefault(tuple(c["connections"][side]), out)

    # ---- registers, $anyseq / $anyconst
    for cname, c in sorted(cells.items()):
        t = c["type"]
        if t == "$dff":
            q = c["connections"]["Q"]
            yn = exact_name(q, prefer_visible=False)
            vis = exact_name(q)
            if not vis and tuple(q) in reset_mux_name:
                vis = reset_mux_name[tuple(q)] + "_ff"
            sig = Signal(_ident(vis or f"r_{len(d.regs)}", used), len(q), "reg", yn)
            reg = Reg(sig, c["connections"]["D"], q, [init_of.get(b) for b in q])
            d.regs.append(reg)
            for k, b in enumerate(q):
                d.driver[b] = (sig, k)
        elif t in ("$anyseq", "$anyconst"):
            y = c["connections"]["Y"]
            vis = exact_name(y)
            yn = exact_name(y, prefer_visible=False)
            if t == "$anyseq":                         # a fresh value every cycle = an input
                sig = Signal(_ident(vis or f"anyseq_{len(d.inputs)}", used), len(y), "input", yn)
                d.inputs.append(sig)
            else:                                      # arbitrary but constant = free register
                sig = Signal(_ident(vis or f"anyconst_{len(d.regs)}", used), len(y), "reg", yn)
                d.regs.append(Reg(sig, list(y), list(y), [None] * len(y), free=True))
            for k, b in enumerate(y):
                d.driver[b] = (sig, k)

    # ---- combinational cells and formal cells
    pending: List[Tuple[str, dict]] = []
    for cname, c in sorted(cells.items()):
        t = c["type"]
        src = _relsrc(c.get("attributes", {}).get("src", cname))
        if t in ("$dff", "$anyseq", "$anyconst"):
            continue
        if t in FORMAL_TYPES:
            label = cname if not cname.startswith("$") else f"{t[1:]}_{len(d.props)}"
            d.props.append(FormalProp(_ident(label, used), t[1:], c["connections"]["A"],
                                      c["connections"]["EN"], src))
            continue
        if t not in COMB_TYPES:
            raise UnsupportedDesign(f"cell type {t} ({src}) not supported yet")
        y = c["connections"]["Y"]
        vis = exact_name(y)
        sig = Signal(_ident(vis or f"w{len(pending)}", used), len(y), "comb", exact_name(y, False))
        for k, b in enumerate(y):
            d.driver[b] = (sig, k)
        pending.append((cname, {"sig": sig, "cell": c, "src": src}))

    # ---- topological order of combinational cells
    out_of = {id(p[1]["sig"]): p for p in pending}
    order: List[CombCell] = []
    state: Dict[str, int] = {}

    def visit(cname: str, entry: dict, stack: List[str]) -> None:
        st = state.get(cname, 0)
        if st == 2:
            return
        if st == 1:
            raise UnsupportedDesign("combinational loop through " + " -> ".join(stack + [cname]))
        state[cname] = 1
        c = entry["cell"]
        for port, bits in c["connections"].items():
            if port == "Y":
                continue
            for b in bits:
                if isinstance(b, int) and b in d.driver:
                    sig = d.driver[b][0]
                    if sig.kind == "comb":
                        dep = out_of[id(sig)]
                        visit(dep[0], dep[1], stack + [cname])
        state[cname] = 2
        order.append(CombCell(entry["sig"], c["type"],
                              {k: _int(v) for k, v in c.get("parameters", {}).items()},
                              c["connections"], entry["src"]))

    for cname, entry in pending:
        visit(cname, entry, [])
    d.comb = order

    # ---- every used bit must have a driver
    def check(bits: List[Bit], where: str) -> None:
        for b in bits:
            if isinstance(b, int) and b not in d.driver:
                raise UnsupportedDesign(f"undriven net bit {b} used by {where}")

    for c in d.comb:
        for port, bits in c.conns.items():
            if port != "Y":
                check(bits, c.src)
    for r in d.regs:
        check(r.d, f"register {r.sig.name}")
    for p in d.props:
        check(p.a + p.en, p.src)
    return d
