"""sv2lean command line.

    python -m sv2lean rtl/counter/counter.sv --top counter \
        --namespace Gen.Counter -o RtlProof/Generated/Counter.lean
    python -m sv2lean rtl/counter/counter.sv --top counter --difftest 20 --cycles 40
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

from . import difftest, emit_lean, frontend, ir


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(prog="sv2lean")
    ap.add_argument("files", nargs="+")
    ap.add_argument("--top", required=True)
    ap.add_argument("-P", "--param", action="append", default=[], metavar="NAME=VALUE")
    ap.add_argument("--namespace", help="Lean namespace (default Gen.<Top>)")
    ap.add_argument("-o", "--output")
    ap.add_argument("--difftest", type=int, metavar="SEEDS",
                    help="compare against Yosys on this many random runs")
    ap.add_argument("--cycles", type=int, default=30)
    a = ap.parse_args(argv)

    params = {}
    for kv in a.param:
        k, v = kv.split("=", 1)
        params[k] = int(v, 0)
    ns = a.namespace or "Gen." + "".join(p.capitalize() for p in a.top.split("_"))

    doc = frontend.netlist_json(a.files, a.top, params)
    design = ir.build(doc["modules"][a.top], a.top)
    note = ", ".join(Path(f).as_posix() for f in a.files)
    if params:
        note += " with " + ", ".join(f"{k}={v}" for k, v in params.items())
    text = emit_lean.emit(design, ns, note)
    for w in sorted(set(design.warnings)):
        print(f"warning: {w}", file=sys.stderr)

    if a.output:
        Path(a.output).parent.mkdir(parents=True, exist_ok=True)
        Path(a.output).write_text(text)
        print(f"wrote {a.output}: {len(design.inputs)} inputs, {len(design.regs)} registers, "
              f"{len(design.comb)} combinational cells, {len(design.props)} formal properties")
    elif not a.difftest:
        sys.stdout.write(text)

    if a.difftest:
        res = difftest.run(doc, design, text, ns, seeds=a.difftest, cycles=a.cycles)
        print(res.summary())
        return 0 if res.ok else 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
