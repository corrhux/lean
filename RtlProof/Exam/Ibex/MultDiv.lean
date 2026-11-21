import RtlProof.Exam.Ibex.Statements
import RtlProof.Meta.Induction
import Std.Tactic.BVDecide

/-!
# Ibex exam, part 1: the multiplier/divider (`ibex_multdiv_slow`)

Your file. Replace each `sorry` with a proof; add any lemmas and definitions you like.
The statements are in `Statements.lean` (do not edit that file or `Spec.lean`).
Each statement is a definition there: start a proof with `unfold Stmt.<name>` (or
`intro …`) to see it in the goal view.

Grade yourself at any time:

    pvs-exam                      # or the Exam view in the web app (pvs-app)

Before you start, read the exam prep chapters in `docs/CAPSTONE_EXAM_PREP.md`, and the
RTL: `third_party/ibex/rtl/ibex_multdiv_slow.sv`. Hints below are the first rung only;
the tutor has the rest of the ladder.
-/

namespace IbexExam
open RtlProof Gen.IbexMD MD

/-- **M1** [10] The FSM state is always one of the seven. Hint: prep chapter E6. -/
theorem md_state_valid : Stmt.md_state_valid := by
  sorry

/-- **M2** [15] A multiply takes 32 cycles. Hint: prep chapter E7; what does the
counter do in COMP? -/
theorem mul_latency : Stmt.mul_latency := by
  sorry

/-- **M3** [10] A divide takes 36 cycles. Hint: reuse what you built for M2. -/
theorem div_latency : Stmt.div_latency := by
  sorry

/-- **M4** [20] Data-independent timing. Hint: prep chapter E8 (two copies). -/
theorem constant_time : Stmt.constant_time := by
  sorry

/-- **Challenge** (no points, no reference proof): the multiplier with the ALU's adder
computes `a * b`. Hint: prep chapter E9. -/
theorem mul_correct : Stmt.mul_correct := by
  sorry

end IbexExam
