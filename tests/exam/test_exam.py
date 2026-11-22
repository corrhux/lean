"""The exam grader: it must score real proofs and refuse everything else."""

import os
import shutil
import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / "tools"))
from pvs_exam import __main__ as exam  # noqa: E402

HAVE_LEAN = bool(os.environ.get("LAKE") or shutil.which("lake") or (Path.home() / ".elan/bin/lake").exists())
pytestmark = pytest.mark.skipif(not HAVE_LEAN, reason="needs Lean")

HEADER = """import RtlProof.Exam.Ibex.Statements
import RtlProof.Meta.Induction
import Std.Tactic.BVDecide
namespace IbexExam
open RtlProof Gen.IbexMD MD
"""


def grade_text(body: str, part: str = "MultDiv"):
    d = REPO / "build" / "tests" / "exam"
    d.mkdir(parents=True, exist_ok=True)
    f = d / f"{part}.lean"
    f.write_text(HEADER + body + "\nend IbexExam\n")
    return {i.name: i for i in exam.grade_file(f, part)}


def test_reference_solutions_score_full_marks():
    r = exam.grade(reference=True)
    assert r["score"] == r["total"] == 100 and not r["tampered"]


def test_blank_exam_scores_zero():
    r = exam.grade()
    assert r["score"] == 0
    assert {i["status"] for i in r["items"]} == {"sorry"}


def test_a_changed_statement_does_not_score():
    items = grade_text("theorem md_state_valid : True := trivial\n")
    assert items["md_state_valid"].status == "missing" and items["md_state_valid"].score == 0
    assert items["mul_latency"].status == "missing"


def test_own_axioms_and_native_decide_do_not_score():
    items = grade_text("axiom cheat : Stmt.md_state_valid\n"
                       "theorem md_state_valid : Stmt.md_state_valid := cheat\n")
    assert items["md_state_valid"].status == "untrusted" and "cheat" in items["md_state_valid"].detail


def test_a_broken_proof_is_failed_with_its_error():
    items = grade_text("theorem md_state_valid : Stmt.md_state_valid := by\n  intro ins n\n  exact rfl\n")
    it = items["md_state_valid"]
    assert it.status == "failed" and it.score == 0 and it.detail


def test_a_real_proof_of_one_item_scores_only_that_item():
    proof = (REPO / "capstone/exam/solutions/MultDiv.lean").read_text()
    start = proof.index("theorem md_state_step")
    end = proof.index("/-! ### M2")
    items = grade_text(proof[start:end])
    assert items["md_state_valid"].status == "proved" and items["md_state_valid"].score == 10
    assert items["mul_latency"].status == "missing"


def test_edited_protected_files_make_the_result_unofficial(monkeypatch, tmp_path):
    h = tmp_path / "hashes"
    h.write_text("0" * 64 + "  RtlProof/Exam/Ibex/Spec.lean\n")
    monkeypatch.setattr(exam, "HASHES_FILE", h)
    assert "RtlProof/Exam/Ibex/Spec.lean" in exam.tampered()
