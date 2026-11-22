import RtlProof.Exam.Ibex.Statements
import RtlProof.Meta.Induction
import Std.Tactic.BVDecide

/-!
# Ibex exam, part 2: the load/store unit (`ibex_load_store_unit`)

Your file. Replace each `sorry` with a proof; add any lemmas and definitions you like.
The statements are in `Statements.lean` (do not edit that file or `Spec.lean`).
Each statement is a definition there: start a proof with `unfold Stmt.<name>` (or
`intro …`) to see it in the goal view.

Grade yourself at any time with `pvs-exam`, or in the web app's Exam view.

Before you start, read the exam prep chapters in `docs/CAPSTONE_EXAM_PREP.md` and the
RTL: `third_party/ibex/rtl/ibex_load_store_unit.sv` (the FSM is near line 440).
-/

namespace IbexExam
open RtlProof Gen.IbexLSU LSU

/-- **L1** [5] A request is held until granted. Hint: prep chapter E6, the first part. -/
theorem lsu_req_held : Stmt.lsu_req_held := by
  sorry

/-- **L2** [15] Stores write what the ISA says. Hint: prep chapter E6; try the
one-cycle claim first and read the counterexample `bv_decide` gives you. -/
theorem lsu_store : Stmt.lsu_store := by
  sorry

/-- **L3** [15] Loads return what the ISA says, however long memory takes. Hint: prep
chapter E7 (unbounded waits). -/
theorem lsu_load : Stmt.lsu_load := by
  sorry

/-- **L4** [10] A misaligned word load. Hint: prep chapter E9. -/
theorem lsu_load_misaligned : Stmt.lsu_load_misaligned := by
  sorry

end IbexExam
