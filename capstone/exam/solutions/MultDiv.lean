import RtlProof.Exam.Ibex.Statements
import RtlProof.Meta.Induction
import Std.Tactic.BVDecide

/-! Reference solution: multiply/divide (M1–M4). SPOILERS. -/

namespace IbexExam
open RtlProof Gen.IbexMD MD

/-! ### M1: the FSM state is always valid -/

theorem md_state_step (s : State) (i : Input) (h : s.md_state_q_ff ≤ 6#3) :
    (step s i).md_state_q_ff ≤ 6#3 := by
  simp only [step, comb] at *
  bv_decide

theorem md_state_valid : Stmt.md_state_valid :=
  Circuit.induction_sound _ _ (fun s => s.md_state_q_ff ≤ 6#3) (by decide)
    (fun s i h => md_state_step s i h) (fun _ h => h)

/-! ### M2, M3: latency -/

/-- The FSM is running an operation: out of reset, enabled, selected, data-independent
timing, result accepted. (Both `MulCycle` and `DivCycle` imply it.) -/
def Busy (i : Input) : Prop :=
  i.rst_ni = 1#1 ∧ (i.mult_en_i = 1#1 ∨ i.div_en_i = 1#1) ∧ (i.mult_sel_i = 1#1 ∨ i.div_sel_i = 1#1) ∧
  i.data_ind_timing_i = 1#1 ∧ i.multdiv_ready_id_i = 1#1

theorem busy_of_mul {op : BitVec 2} {i : Input} (h : MulCycle op i) : Busy i := by
  obtain ⟨h1, h2, h3, -, -, -, h7, h8⟩ := h
  exact ⟨h1, Or.inl h2, Or.inl h3, h7, h8⟩

theorem busy_of_div {op : BitVec 2} {i : Input} (h : DivCycle op i) : Busy i := by
  obtain ⟨h1, h2, h3, -, -, -, h7, h8⟩ := h
  exact ⟨h1, Or.inr h2, Or.inr h3, h7, h8⟩

/-- In COMP the counter counts down, and at 1 the FSM moves on to LAST. -/
theorem comp_step (s : State) (i : Input) (hb : Busy i) (hs : s.md_state_q_ff = COMP) :
    (step s i).multdiv_count_q_ff = s.multdiv_count_q_ff - 1#5 ∧
    (s.multdiv_count_q_ff = 1#5 → (step s i).md_state_q_ff = LAST) ∧
    (s.multdiv_count_q_ff ≠ 1#5 → (step s i).md_state_q_ff = COMP) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hb
  simp only [step, comb] at *
  bv_decide

/-- Thirty-one COMP cycles: if cycle `m` is COMP with count 31, cycle `m + j` is COMP with
count `31 - j` (for `j ≤ 30`), and cycle `m + 31` is LAST. -/
theorem countdown (ins : Nat → Input) (r : Nat → State)
    (hr : ∀ n, r (n + 1) = step (r n) (ins n)) (hb : ∀ n, Busy (ins n)) (m : Nat)
    (hm : (r m).md_state_q_ff = COMP ∧ (r m).multdiv_count_q_ff = 31#5) :
    (∀ j, j ≤ 30 → (r (m + j)).md_state_q_ff = COMP ∧ (r (m + j)).multdiv_count_q_ff.toNat = 31 - j) ∧
    (r (m + 31)).md_state_q_ff = LAST := by
  have phase : ∀ j, j ≤ 30 → (r (m + j)).md_state_q_ff = COMP ∧
      (r (m + j)).multdiv_count_q_ff.toNat = 31 - j := by
    intro j
    induction j with
    | zero => intro _; simp [hm.1, hm.2]
    | succ j ih =>
      intro hj
      obtain ⟨hs, hc⟩ := ih (by omega)
      obtain ⟨hcnt, -, hcomp⟩ := comp_step (r (m + j)) (ins (m + j)) (hb _) hs
      have hne : (r (m + j)).multdiv_count_q_ff ≠ 1#5 := by
        intro h; rw [h] at hc; simp at hc; omega
      rw [show m + (j + 1) = (m + j) + 1 by omega, hr]
      refine ⟨hcomp hne, ?_⟩
      rw [hcnt, BitVec.toNat_sub, hc]
      simp; omega
  refine ⟨phase, ?_⟩
  obtain ⟨hs, hc⟩ := phase 30 (by omega)
  obtain ⟨-, hlast, -⟩ := comp_step (r (m + 30)) (ins (m + 30)) (hb _) hs
  have h1 : (r (m + 30)).multdiv_count_q_ff = 1#5 := by
    apply BitVec.eq_of_toNat_eq; rw [hc]; rfl
  rw [show m + 31 = (m + 30) + 1 by omega, hr]
  exact hlast h1

theorem idle_step_mul {op : BitVec 2} (s : State) (i : Input) (h : MulCycle op i)
    (hop : op = MULL ∨ op = MULH) (hs : s.md_state_q_ff = IDLE) :
    (step s i).md_state_q_ff = COMP ∧ (step s i).multdiv_count_q_ff = 31#5 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  simp only [step, comb] at *
  rcases hop with hop | hop <;> subst hop <;> bv_decide

theorem valid_mul {op : BitVec 2} (s : State) (i : Input) (h : MulCycle op i)
    (hop : op = MULL ∨ op = MULH) :
    ((s.md_state_q_ff = IDLE ∨ s.md_state_q_ff = COMP) → valid s i = 0#1) ∧
    (s.md_state_q_ff = LAST → valid s i = 1#1) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  simp only [valid, outputs, comb] at *
  rcases hop with hop | hop <;> subst hop <;> bv_decide

theorem mul_latency : Stmt.mul_latency := by
  intro op hop s0 h0 ins hin
  let r := (circuit s0).run ins
  have hr : ∀ n, r (n + 1) = step (r n) (ins n) := fun n => rfl
  have h1 := idle_step_mul s0 (ins 0) (hin 0) hop h0
  obtain ⟨phase, hlast⟩ := countdown ins r hr (fun n => busy_of_mul (hin n)) 1 h1
  refine ⟨fun k hk => ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact (valid_mul s0 (ins 0) (hin 0) hop).1 (Or.inl h0)
    · have := (phase (k - 1) (by omega)).1
      rw [show 1 + (k - 1) = k by omega] at this
      exact (valid_mul (r k) (ins k) (hin k) hop).1 (Or.inr this)
  · exact (valid_mul (r 32) (ins 32) (hin 32) hop).2 hlast

theorem div_steps {op : BitVec 2} (s : State) (i : Input) (h : DivCycle op i)
    (hop : op = DIV ∨ op = REM) :
    (s.md_state_q_ff = IDLE → (step s i).md_state_q_ff = ABS_A ∧ (step s i).multdiv_count_q_ff = 31#5) ∧
    (s.md_state_q_ff = ABS_A → (step s i).md_state_q_ff = ABS_B ∧
      (step s i).multdiv_count_q_ff = s.multdiv_count_q_ff) ∧
    (s.md_state_q_ff = ABS_B → (step s i).md_state_q_ff = COMP ∧
      (step s i).multdiv_count_q_ff = s.multdiv_count_q_ff) ∧
    (s.md_state_q_ff = LAST → (step s i).md_state_q_ff = CHANGE_SIGN) ∧
    (s.md_state_q_ff = CHANGE_SIGN → (step s i).md_state_q_ff = FINISH) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  simp only [step, comb] at *
  rcases hop with hop | hop <;> subst hop <;> bv_decide

theorem valid_div {op : BitVec 2} (s : State) (i : Input) (h : DivCycle op i)
    (hop : op = DIV ∨ op = REM) :
    (s.md_state_q_ff ≠ FINISH → valid s i = 0#1) ∧ (s.md_state_q_ff = FINISH → valid s i = 1#1) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  simp only [valid, outputs, comb] at *
  rcases hop with hop | hop <;> subst hop <;> bv_decide

theorem div_latency : Stmt.div_latency := by
  intro op hop s0 h0 ins hin
  let r := (circuit s0).run ins
  have hr : ∀ n, r (n + 1) = step (r n) (ins n) := fun n => rfl
  have st := fun n => div_steps (r n) (ins n) (hin n) hop
  -- `r (n + 1)` is `step (r n) (ins n)` by definition, so each fact can be stated about `r (n + 1)`
  have h1s : (r 1).md_state_q_ff = ABS_A := ((st 0).1 h0).1
  have h1c : (r 1).multdiv_count_q_ff = 31#5 := ((st 0).1 h0).2
  have h2s : (r 2).md_state_q_ff = ABS_B := ((st 1).2.1 h1s).1
  have h2c : (r 2).multdiv_count_q_ff = 31#5 := ((st 1).2.1 h1s).2.trans h1c
  have h3 : (r 3).md_state_q_ff = COMP ∧ (r 3).multdiv_count_q_ff = 31#5 :=
    ⟨((st 2).2.2.1 h2s).1, ((st 2).2.2.1 h2s).2.trans h2c⟩
  obtain ⟨phase, hlast⟩ := countdown ins r hr (fun n => busy_of_div (hin n)) 3 h3
  have h35 : (r 35).md_state_q_ff = CHANGE_SIGN := (st 34).2.2.2.1 hlast
  have h36 : (r 36).md_state_q_ff = FINISH := (st 35).2.2.2.2 h35
  have ne : ∀ k, k < 36 → (r k).md_state_q_ff ≠ FINISH := by
    intro k hk
    have cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ (3 ≤ k ∧ k ≤ 33) ∨ k = 34 ∨ k = 35 := by omega
    rcases cases with rfl | rfl | rfl | ⟨ha, hb⟩ | rfl | rfl
    · rw [show r 0 = s0 from rfl, h0]; decide
    · rw [h1s]; decide
    · rw [h2s]; decide
    · have := (phase (k - 3) (by omega)).1
      rw [show 3 + (k - 3) = k by omega] at this
      rw [this]; decide
    · rw [hlast]; decide
    · rw [h35]; decide
  exact ⟨fun k hk => (valid_div (r k) (ins k) (hin k) hop).1 (ne k hk),
         (valid_div (r 36) (ins 36) (hin 36) hop).2 h36⟩

/-! ### M4: data-independent timing -/

/-- One step, two copies: equal control state and control inputs give equal control state
next cycle and the same `valid_o` now. -/
theorem ctl_step (s t : State) (i j : Input) (hs : ctl s = ctl t) (hi : ctlIn i = ctlIn j)
    (hd : i.data_ind_timing_i = 1#1) :
    ctl (step s i) = ctl (step t j) ∧ valid s i = valid t j := by
  simp only [ctl, ctlIn, Prod.mk.injEq] at hs hi ⊢
  obtain ⟨hs1, hs2⟩ := hs
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hi
  simp only [valid, step, outputs, comb] at *
  bv_decide

theorem constant_time : Stmt.constant_time := by
  intro s t hst ins jns hctl hd n
  have h : ∀ n, ctl ((circuit s).run ins n) = ctl ((circuit t).run jns n) := by
    intro n
    induction n with
    | zero => exact hst
    | succ n ih => exact (ctl_step _ _ _ _ ih (hctl n) (hd n)).1
  exact ⟨h n, (ctl_step _ _ _ _ (h n) (hctl n) (hd n)).2⟩

end IbexExam
