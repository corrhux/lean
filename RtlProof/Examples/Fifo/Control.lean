import Std.Tactic.BVDecide

/-!
# FIFO control logic, for every depth (course D5)

An abstract model of `rtl/fifo/fifo.sv`'s pointers and counter, with the depth
`2 ^ aw` as a **parameter**. `inv_step` proves the control invariant is
preserved for *every* `aw`, which no model checker can do: each run fixes
`AW`. `Solution.lean` links this to the generated RTL model at `AW = 2`.

The invariant is the same "helper assertion" a model checker needs:
`count ≤ DEPTH` and `wptr = rptr + count (mod DEPTH)`.

No SAT here: these are hand-written proofs over symbolic widths, with
`#print axioms` showing only Lean's three standard axioms.
-/

namespace RtlProof.Fifo

/-- The control state: read and write pointers and the occupancy counter. -/
structure Ctl (aw : Nat) where
  rptr : BitVec aw
  wptr : BitVec aw
  count : BitVec (aw + 1)

variable {aw : Nat}

def Ctl.full (s : Ctl aw) : Bool := s.count == BitVec.ofNat (aw + 1) (2 ^ aw)
def Ctl.empty (s : Ctl aw) : Bool := s.count == 0

/-- One clock edge of the control logic (same equations as the RTL). -/
def step (s : Ctl aw) (rst push pop : Bool) : Ctl aw :=
  bif rst then ⟨0, 0, 0⟩ else
    let dpush := push && !s.full
    let dpop := pop && !s.empty
    { rptr := bif dpop then s.rptr + 1 else s.rptr
      wptr := bif dpush then s.wptr + 1 else s.wptr
      count := s.count + (bif dpush then 1 else 0) - (bif dpop then 1 else 0) }

/-- The control invariant. -/
def Inv (s : Ctl aw) : Prop :=
  s.count.toNat ≤ 2 ^ aw ∧ s.wptr = s.rptr + s.count.setWidth aw

theorem two_pow_lt : 2 ^ aw < 2 ^ (aw + 1) := by
  have := Nat.two_pow_pos aw
  rw [Nat.pow_succ]; omega

theorem full_iff (s : Ctl aw) : s.full = true ↔ s.count.toNat = 2 ^ aw := by
  simp only [Ctl.full, beq_iff_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt two_pow_lt]

theorem empty_iff (s : Ctl aw) : s.empty = true ↔ s.count.toNat = 0 := by
  simp [Ctl.empty, ← BitVec.toNat_inj]

theorem setWidth_sub' {w i : Nat} (x y : BitVec w) (h : i ≤ w) :
    (x - y).setWidth i = x.setWidth i - y.setWidth i := by
  have := BitVec.setWidth_add (x - y) y h
  rw [BitVec.sub_add_cancel] at this
  rw [this, BitVec.add_sub_cancel]

theorem setWidth_one' : (1 : BitVec (aw + 1)).setWidth aw = 1 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat]

theorem toNat_one' : (1 : BitVec (aw + 1)).toNat = 1 := BitVec.toNat_one (by omega)

theorem toNat_succ (c : BitVec (aw + 1)) (h : c.toNat < 2 ^ aw) : (c + 1).toNat = c.toNat + 1 := by
  have := two_pow_lt (aw := aw)
  rw [BitVec.toNat_add, toNat_one']
  exact Nat.mod_eq_of_lt (by omega)

theorem toNat_pred (c : BitVec (aw + 1)) (h : 0 < c.toNat) : (c - 1).toNat = c.toNat - 1 := by
  have := c.isLt
  rw [BitVec.toNat_sub, toNat_one']
  have e : 2 ^ (aw + 1) - 1 + c.toNat = 2 ^ (aw + 1) + (c.toNat - 1) := by omega
  rw [e, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

/-! The four non-reset transitions. -/

theorem inv_push (s : Ctl aw) (h : Inv s) (hf : s.count.toNat ≠ 2 ^ aw) :
    Inv ⟨s.rptr, s.wptr + 1, s.count + 1⟩ := by
  obtain ⟨hc, hp⟩ := h
  refine ⟨?_, ?_⟩
  · simp only; rw [toNat_succ _ (by omega)]; omega
  · simp only; rw [BitVec.setWidth_add _ _ (by omega), setWidth_one', hp, BitVec.add_assoc]

theorem inv_pop (s : Ctl aw) (h : Inv s) (he : s.count.toNat ≠ 0) :
    Inv ⟨s.rptr + 1, s.wptr, s.count - 1⟩ := by
  obtain ⟨hc, hp⟩ := h
  refine ⟨?_, ?_⟩
  · simp only; rw [toNat_pred _ (by omega)]; omega
  · simp only
    rw [setWidth_sub' _ _ (by omega), setWidth_one', hp, BitVec.add_assoc,
      BitVec.add_comm 1, BitVec.sub_add_cancel]

theorem inv_both (s : Ctl aw) (h : Inv s) :
    Inv ⟨s.rptr + 1, s.wptr + 1, s.count + 1 - 1⟩ := by
  obtain ⟨hc, hp⟩ := h
  refine ⟨?_, ?_⟩
  · simp only [BitVec.add_sub_cancel]; exact hc
  · simp only [BitVec.add_sub_cancel]
    rw [hp]; ac_rfl

/-! The same transitions in the shape `step` produces (`count + dpush - dpop`). -/

theorem inv_hold' (s : Ctl aw) (h : Inv s) : Inv ⟨s.rptr, s.wptr, s.count + 0 - 0⟩ := by
  have e : s.count + 0 - 0 = s.count := by simp
  rw [e]; exact h

theorem inv_push' (s : Ctl aw) (h : Inv s) (hf : s.count.toNat ≠ 2 ^ aw) :
    Inv ⟨s.rptr, s.wptr + 1, s.count + 1 - 0⟩ := by
  have e : s.count + 1 - 0 = s.count + 1 := by simp
  rw [e]; exact inv_push s h hf

theorem inv_pop' (s : Ctl aw) (h : Inv s) (he : s.count.toNat ≠ 0) :
    Inv ⟨s.rptr + 1, s.wptr, s.count + 0 - 1⟩ := by
  have e : s.count + 0 - 1 = s.count - 1 := by simp
  rw [e]; exact inv_pop s h he

/-- **The FIFO control invariant is preserved by every step, for every depth `2 ^ aw`.** -/
theorem inv_step (s : Ctl aw) (rst push pop : Bool) (h : Inv s) : Inv (step s rst push pop) := by
  unfold step
  cases rst
  · have hf := full_iff s
    have he := empty_iff s
    cases push <;> cases pop <;> cases hfs : s.full <;> cases hes : s.empty <;>
      simp only [hfs, hes, Bool.not_true, Bool.not_false, Bool.and_true, Bool.and_false,
        Bool.false_eq_true, Bool.cond_true, Bool.cond_false] at hf he ⊢
    all_goals first
      | exact inv_hold' s h
      | exact inv_push' s h (fun e => hf.mpr e)
      | exact inv_pop' s h (fun e => he.mpr e)
      | exact inv_both s h
  · exact ⟨by simp, by simp⟩

theorem inv_reset (s : Ctl aw) (push pop : Bool) : Inv (step s true push pop) := by
  simp [step, Inv]

/-- The three RTL assertions, for every depth. -/
theorem count_le (s : Ctl aw) (h : Inv s) : s.count.toNat ≤ 2 ^ aw := h.1

theorem ptrs (s : Ctl aw) (h : Inv s) : s.wptr - s.rptr = s.count.setWidth aw := by
  rw [h.2, BitVec.add_comm, BitVec.add_sub_cancel]

theorem not_full_and_empty (s : Ctl aw) : ¬ (s.full = true ∧ s.empty = true) := by
  rw [full_iff, empty_iff]
  have := Nat.two_pow_pos aw
  omega

end RtlProof.Fifo
