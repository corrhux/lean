import RtlProof.Exam.Ibex.Statements
import RtlProof.Meta.Induction
import Std.Tactic.BVDecide

/-! Reference solution: load/store unit (L1–L4). SPOILERS. -/

namespace IbexExam
open RtlProof Gen.IbexLSU LSU

/-! ### L1: requests are held until granted -/

theorem lsu_req_held : Stmt.lsu_req_held := by
  intro s i hl hs
  simp only [Live, outputs, step, comb] at *
  rcases hs with hs | hs <;> bv_decide

/-! ### L2: stores, in every reachable state -/

/-- What the store proof needs to know about reachable states: the CHERIoT states are
never entered, and in IDLE (and in the state that returns to it) no split access is in
flight. Not true of every state: in WAIT_RVALID_MIS `handle_misaligned_q` is set. -/
def Inv (s : State) : Prop :=
  s.ls_fsm_cs_ff ≤ 4#4 ∧
  ((s.ls_fsm_cs_ff = IDLE ∨ s.ls_fsm_cs_ff = WAIT_RVALID_MIS_GNTS_DONE) → s.handle_misaligned_q_ff = 0#1)

theorem inv_step (s : State) (i : Input) (hl : Live i) (h : Inv s) : Inv (step s i) := by
  simp only [Inv, Live, step, comb] at *
  bv_decide

theorem inv_run (ins : Nat → Input) (hl : ∀ n, Live (ins n)) :
    ∀ n, Inv ((circuit init0).run ins n) := by
  intro n
  induction n with
  | zero => show Inv init0; simp only [Inv]; decide
  | succ n ih => exact inv_step _ _ (hl n) ih

theorem store_ok (s : State) (i : Input) (hinv : Inv s) (hl : Live i) (hs : s.ls_fsm_cs_ff = IDLE)
    (hreq : i.lsu_req_i = 1#1) (hwe : i.lsu_we_i = 1#1) (hf : Fits i.adder_result_ex_i i.lsu_type_i)
    (old : BitVec 32) :
    (outputs s i).data_req_o = 1#1 ∧ (outputs s i).data_we_o = 1#1 ∧
    (outputs s i).data_addr_o = wordAddr i.adder_result_ex_i ∧
    busWrite old (outputs s i).data_be_o (outputs s i).data_wdata_o =
      storeSpec old i.adder_result_ex_i i.lsu_type_i i.lsu_wdata_i := by
  simp only [Inv, Live, Fits, off, wordAddr, busWrite, byteMask, storeSpec, sizeMask, bits,
    outputs, comb] at *
  bv_decide

theorem lsu_store : Stmt.lsu_store := by
  intro ins hl n s i hs hreq hwe hf o
  have h := fun old => store_ok s i (inv_run ins hl n) (hl n) hs hreq hwe hf old
  exact ⟨(h 0).1, (h 0).2.1, (h 0).2.2.1, fun old => (h old).2.2.2⟩

/-! ### L3: loads, however long memory takes -/

/-- A load is outstanding: IDLE, no error recorded, and the access registered. -/
def Pending (s : State) (o t : BitVec 2) (x : BitVec 1) : Prop :=
  s.ls_fsm_cs_ff = IDLE ∧ s.rdata_offset_q_ff = o ∧ s.data_type_q_ff = t ∧ s.data_sign_ext_q_ff = x ∧
  s.data_we_q_ff = 0#1 ∧ s.lsu_err_q_ff = 0#1 ∧ s.pmp_err_q_ff = 0#1 ∧ s.lsu_intg_err_q_ff = 0#1

theorem issue (s : State) (i : Input) (hl : Live i) (hs : s.ls_fsm_cs_ff = IDLE)
    (hreq : i.lsu_req_i = 1#1) (hwe : i.lsu_we_i = 0#1) (hg : i.data_gnt_i = 1#1)
    (hp : i.data_pmp_err_i = 0#1) (hf : Fits i.adder_result_ex_i i.lsu_type_i) :
    Pending (step s i) (off i.adder_result_ex_i) i.lsu_type_i i.lsu_sign_ext_i := by
  simp only [Pending, Live, Fits, off, step, comb] at *
  bv_decide

theorem wait (s : State) (i : Input) (o t : BitVec 2) (x : BitVec 1) (hl : Live i)
    (hp : Pending s o t x) (hreq : i.lsu_req_i = 0#1) (hv : i.data_rvalid_i = 0#1) :
    Pending (step s i) o t x := by
  simp only [Pending, Live, step, comb] at *
  bv_decide

theorem respond (s : State) (i : Input) (a : BitVec 32) (t : BitVec 2) (x : BitVec 1) (hl : Live i)
    (hp : Pending s (off a) t x) (hf : Fits a t) (hv : i.data_rvalid_i = 1#1) (he : i.data_bus_err_i = 0#1) :
    (outputs s i).lsu_rdata_valid_o = 1#1 ∧ (outputs s i).lsu_rdata_o = loadSpec i.data_rdata_i a t x := by
  simp only [Pending, Live, Fits, off, loadSpec, bits, outputs, comb] at *
  bv_decide

theorem lsu_load : Stmt.lsu_load := by
  intro s ins k hs hl hreq hwe hg hp hf hwait hv he
  let r := (circuit s).run ins
  have h1 : Pending (r 1) (off (ins 0).adder_result_ex_i) (ins 0).lsu_type_i (ins 0).lsu_sign_ext_i :=
    issue s (ins 0) (hl 0) hs hreq hwe hg hp hf
  have hw : ∀ j, j ≤ k → Pending (r (j + 1)) (off (ins 0).adder_result_ex_i) (ins 0).lsu_type_i
      (ins 0).lsu_sign_ext_i := by
    intro j
    induction j with
    | zero => intro _; exact h1
    | succ j ih =>
      intro hj
      obtain ⟨hr0, hv0⟩ := hwait (j + 1) (by omega) hj
      exact wait _ _ _ _ _ (hl _) (ih (by omega)) hr0 hv0
  exact respond _ _ _ _ _ (hl _) (hw k (Nat.le_refl k)) hf hv he

/-! ### L4: a misaligned word load -/

theorem lsu_load_misaligned : Stmt.lsu_load_misaligned := by
  intro s ins a hs hl ho hreq hwe ht ha hg hp ha1 hv1 he1 hg1 hp1 hreq2 hv2 he2 o1 o2
  have l0 := hl 0; have l1 := hl 1; have l2 := hl 2
  show (outputs (step s (ins 0)) (ins 1)).addr_incr_req_o = 1#1 ∧ _
  simp only [Live, off, wordAddr, loadWordSpan, o1, o2, Circuit.run, circuit, outputs, step, comb] at *
  subst ha
  bv_decide

end IbexExam
