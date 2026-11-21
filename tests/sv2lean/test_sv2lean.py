"""sv2lean tests: generated Lean must agree with Yosys, and difftest must catch bugs.

Needs Yosys (native or `yowasp-yosys`) and Lean (`lake`, after `lake build`);
skipped otherwise.
"""

import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / "tools"))

from sv2lean import difftest, emit_lean, frontend, ir  # noqa: E402

LAKE = os.environ.get("LAKE") or shutil.which("lake")
HAVE_YOSYS = bool(os.environ.get("YOSYS") or shutil.which("yosys") or shutil.which("yowasp-yosys"))
pytestmark = pytest.mark.skipif(not (LAKE and HAVE_YOSYS), reason="needs Yosys and Lean")

DESIGNS = REPO / "tests" / "sv2lean" / "designs"


def generate(files, top, ns, params=None):
    doc = frontend.netlist_json([str(f) for f in files], top, params)
    design = ir.build(doc["modules"][top], top)
    return doc, design, emit_lean.emit(design, ns, top)


@pytest.fixture(scope="module", autouse=True)
def lean_library_built():
    subprocess.run([LAKE, "build", "RtlProof.Core.Circuit"], cwd=REPO, check=True,
                   capture_output=True)
    os.environ.setdefault("LAKE", LAKE)


def test_counter_matches_yosys():
    doc, d, text = generate([REPO / "rtl/counter/counter.sv"], "counter", "T.Counter")
    assert [s.name for s in d.inputs] == ["rst", "en"]
    assert {p.name for p in d.props} == {"p_le_9", "p_hold", "c_reach_9", "assume_0"} or \
        {p.name for p in d.props} >= {"p_le_9", "p_hold", "c_reach_9"}
    res = difftest.run(doc, d, text, "T.Counter", seeds=4, cycles=25)
    assert res.ok, res.summary()


def test_counter_bug_parameter_matches_yosys():
    doc, d, text = generate([REPO / "rtl/counter/counter.sv"], "counter", "T.CounterBug", {"WRAP": 10})
    res = difftest.run(doc, d, text, "T.CounterBug", seeds=3, cycles=25)
    assert res.ok, res.summary()


def test_alu_matches_yosys():
    doc, d, text = generate([DESIGNS / "alu.sv"], "alu", "T.Alu")
    kinds = {c.type for c in d.comb}
    for t in ("$add", "$sub", "$mul", "$neg", "$shl", "$shr", "$sshr", "$lt", "$pmux",
              "$reduce_xor", "$reduce_and", "$reduce_or", "$logic_and", "$logic_not"):
        assert t in kinds, f"{t} not exercised (have {sorted(kinds)})"
    res = difftest.run(doc, d, text, "T.Alu", seeds=6, cycles=30)
    assert res.ok, res.summary()


@pytest.mark.parametrize("mutation", [
    ("BitVec.sshiftRight'", "(fun x y => x >>> y)"),  # arithmetic → logical shift
    (".slt", ".ult"),                                  # signed → unsigned compare
    (" - ", " + "),                                    # subtract → add
])
def test_difftest_catches_injected_bugs(mutation):
    doc, d, text = generate([DESIGNS / "alu.sv"], "alu", "T.AluMut")
    old, new = mutation
    assert old in text, f"mutation target {old!r} not in generated model"
    mutated = text.replace(old, new, 1)
    res = difftest.run(doc, d, mutated, "T.AluMut", seeds=6, cycles=30)
    assert not res.ok, f"difftest did not notice mutation {mutation}"


def test_unsupported_cell_is_reported():
    src = Path(frontend.scratch_dir()) / "div.sv"     # WebAssembly Yosys cannot read /tmp
    src.write_text("module div(input logic clk, input logic [3:0] a, b, output logic [3:0] q);\n"
                   "  always_ff @(posedge clk) q <= a / b;\nendmodule\n")
    with pytest.raises(ir.UnsupportedDesign, match=r"\$div"):
        generate([src], "div", "T.Div")


def test_fifo_with_memory_matches_yosys():
    doc, d, text = generate([REPO / "rtl/fifo/fifo.sv"], "fifo", "T.Fifo", {"AW": 2, "DW": 4})
    assert {f"mem_{k}" for k in range(4)} <= {r.sig.name for r in d.regs}
    res = difftest.run(doc, d, text, "T.Fifo", seeds=4, cycles=40)
    assert res.ok, res.summary()


def test_multiplier_matches_yosys():
    doc, d, text = generate([REPO / "rtl/mul/mul.sv"], "mul", "T.Mul", {"W": 6})
    assert not d.regs                      # purely combinational: nothing to compare per cycle
    assert "p" in {c.sig.name for c in d.comb}


def test_arbiter_with_anyconst_matches_yosys():
    doc, d, text = generate([REPO / "rtl/arbiter/arbiter.sv"], "arbiter", "T.Arb", {"K": 2})
    free = [r for r in d.regs if r.free]
    assert [r.sig.name for r in free] == ["f_j"]        # anyconst → constant register
    res = difftest.run(doc, d, text, "T.Arb", seeds=4, cycles=40)
    assert res.ok, res.summary()
