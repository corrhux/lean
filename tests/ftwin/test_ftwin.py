import json
import os
import shutil
import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / "tools"))

from ftwin.__main__ import main  # noqa: E402

HAVE = (shutil.which("sby") or shutil.which("yowasp-sby")) and (os.environ.get("LAKE") or shutil.which("lake"))
pytestmark = pytest.mark.skipif(not HAVE, reason="needs SymbiYosys and Lean")


def test_counter_twin_report(tmp_path):
    out = tmp_path / "counter.json"
    assert main(["run", "counter", "--json", str(out)]) == 0
    rows = json.loads(out.read_text())
    got = {(r["property"], r["side"], r["task"]): r["status"] for r in rows}
    assert got[("p_le_9", "mc", "bmc")] == "bounded"
    assert got[("p_le_9", "mc", "prove")] == "proven"
    assert got[("p_le_9", "mc", "bug")] == "cex"
    assert got[("c_reach_9", "mc", "cover")] == "covered"
    lean = {r["property"]: r for r in rows if r["side"] == "lean"}
    for prop in ("p_le_9", "p_hold"):
        assert lean[prop]["status"] == "proved"
        assert "sorryAx" not in lean[prop]["axioms"]
    bug = next(r for r in rows if r["task"] == "bug" and r["property"] == "p_le_9")
    assert bug["depth"] == 11 and bug["cex_vcd"].endswith("trace.vcd")
