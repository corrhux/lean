"""Tutor tools and prompt assembly, without calling the API."""

import os
import shutil
import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / "tools"))

from tutor import prompts, tools  # noqa: E402

HAVE_LEAN = bool(os.environ.get("LAKE") or shutil.which("lake"))


def test_course_lookup_finds_lessons():
    out = tools.course_lookup("L12 induction")
    assert "LEAN_FLUENCY.md" in out and "generalizing" in out
    assert "No course section" in tools.course_lookup("zzzz-no-such-thing")


def test_read_file_is_sandboxed():
    assert "module counter" in tools.read_file("rtl/counter/counter.sv")
    assert tools.read_file("../etc/passwd").startswith("Refused")
    assert tools.read_file(".git/config").startswith("Refused")
    assert tools.read_file("docs/nope.md").startswith("No such file")


def test_vcd_parser_and_summary(tmp_path):
    vcd = REPO / "build" / "tutor_test.vcd"
    vcd.parent.mkdir(exist_ok=True)
    vcd.write_text("""$timescale 1ns $end
$scope module counter $end
$var wire 1 ! en $end
$var wire 4 " cnt [3:0] $end
$upscope $end
$enddefinitions $end
#0
1!
b0111 "
#5
#10
b1000 "
#15
#20
b1001 "
""")
    sigs, steps = tools.parse_vcd(vcd.read_text())
    assert sigs['"'] == ("cnt", 4)
    table = tools.cex_summary("build/tutor_test.vcd")
    assert "cnt" in table and " 7" in table and " 9" in table


def test_system_prompt_is_static_and_has_rosetta():
    a, b = prompts.system_prompt(), prompts.system_prompt()
    assert a == b                                  # identical bytes → cacheable
    assert "assert property" in a and "check_lean" in a
    for k in prompts.LADDER:
        assert f"  {k}." in a


def test_user_message_carries_level_and_file():
    msg = prompts.user_message("why?", 3, file="rtl/counter/counter.sv", design="counter")
    assert msg.startswith("Hint level: 3") and "module counter" in msg and "rtl/counter" in msg


@pytest.mark.skipif(not HAVE_LEAN, reason="needs Lean")
def test_check_lean_reports_success_errors_and_sorry():
    ok = tools.check_lean("example : 2 + 2 = 4 := rfl")
    assert ok["ok"] and not ok["errors"]
    bad = tools.check_lean("example (n : Nat) : 0 + n = n := rfl")
    assert not bad["ok"] and "Type mismatch" in bad["errors"][0]
    hole = tools.check_lean("theorem t : 1 = 1 := by sorry")
    assert hole["uses_sorry"]
    project = tools.check_lean("import RtlProof\n#check Gen.Counter.p_le_9_holds")
    assert project["ok"], project
