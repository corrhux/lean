import RtlProof.Generated.Fifo4
import RtlProof.Examples.Fifo.Control
import RtlProof.Meta.Induction
import Std.Tactic.BVDecide

/-!
# FIFO twin (course D5): the RTL at `AW = 2`, via the all-depths proof

`Gen.Fifo4` is generated from `rtl/fifo/fifo.sv` with `AW = 2` (4 entries) and
`DW = 4`. The memory becomes four registers, `mem_0` to `mem_3`.

The structure is the one the course teaches for parameterized designs:

1. `RtlProof.Fifo.inv_step` (Control.lean): the control invariant holds for
   **every** depth. This is a hand proof with no SAT.
2. `link`: one clock edge of the generated RTL model is one step of that
   abstract control model. This is width-specific and discharged by
   `bv_decide`, but it is *structural*, so it is easy.
3. The RTL assertions follow by `safePrefix_of_inv`.

Compare `p_count_le_by_sat`, which proves the same assertion with a
fixed-width invariant and `bv_decide` only. That works at 4 entries but has to
be redone for every depth.
-/

namespace Gen.Fifo4
open RtlProof RtlProof.Circuit

/-- The abstraction function: which RTL registers make up the control state. -/
def ctlOf (s : State) : RtlProof.Fifo.Ctl 2 := ⟨s.rptr, s.wptr, s.count⟩

/-- **Link lemma.** The generated netlist's control registers step exactly like the
abstract model instantiated at `aw = 2`. -/
theorem link (s : State) (i : Input) :
    ctlOf (step s i) =
      RtlProof.Fifo.step (ctlOf s) (i.rst == 1#1) (i.push == 1#1) (i.pop == 1#1) := by
  simp only [ctlOf, step, comb, RtlProof.Fifo.step, RtlProof.Fifo.Ctl.full, RtlProof.Fifo.Ctl.empty]
  cases hr : (i.rst == 1#1) <;>
    simp only [Bool.cond_true, Bool.cond_false, RtlProof.Fifo.Ctl.mk.injEq] <;>
    refine ⟨?_, ?_, ?_⟩ <;> bv_decide

/-- The RTL invariant: after the first (reset) cycle, the abstract invariant holds. -/
def InvG (s : State) : Prop := s.f_past_valid = 1#1 → RtlProof.Fifo.Inv (ctlOf s)

theorem invG_init (s0 : State) (h0 : initOK s0) : InvG s0 := by
  intro h
  simp only [initOK] at h0
  rw [h0] at h
  exact absurd h (by decide)

theorem invG_step (s : State) (i : Input) (hI : InvG s) (hA : assumptions s i) :
    InvG (step s i) := by
  intro _
  rw [link]
  by_cases hv : s.f_past_valid = 1#1
  · exact RtlProof.Fifo.inv_step _ _ _ _ (hI hv)
  · -- first cycle: the assumption forces reset
    have hr : (i.rst == 1#1) = true := by
      simp only [assumptions, comb] at hA
      bv_decide
    rw [hr]
    exact RtlProof.Fifo.inv_reset _ _ _

/-- From the abstract invariant (stated with `toNat`) to the bit-level facts. -/
theorem bits_of_inv (s : State) (h : RtlProof.Fifo.Inv (ctlOf s)) :
    s.count ≤ 4#3 ∧ s.wptr = s.rptr + s.count.setWidth 2 := by
  obtain ⟨hc, hp⟩ := h
  exact ⟨by rw [BitVec.le_def]; simpa [ctlOf] using hc, hp⟩

theorem p_count_le_holds (s0 : State) (h0 : initOK s0) :
    (circuit s0).SafePrefix assumptions p_count_le := by
  refine safePrefix_of_inv _ _ _ InvG (invG_init s0 h0) invG_step ?_
  intro s i hI _
  simp only [p_count_le, comb]
  intro hv
  have ⟨hc, _⟩ := bits_of_inv s (hI (by bv_decide))
  bv_decide

theorem p_ptrs_holds (s0 : State) (h0 : initOK s0) :
    (circuit s0).SafePrefix assumptions p_ptrs := by
  refine safePrefix_of_inv _ _ _ InvG (invG_init s0 h0) invG_step ?_
  intro s i hI _
  simp only [p_ptrs, comb]
  intro hv
  have ⟨_, hp⟩ := bits_of_inv s (hI (by bv_decide))
  bv_decide

theorem p_not_full_and_empty_holds (s0 : State) (h0 : initOK s0) :
    (circuit s0).SafePrefix assumptions p_not_full_and_empty := by
  refine safePrefix_of_inv _ _ _ InvG (invG_init s0 h0) invG_step ?_
  intro s i _ _
  simp only [p_not_full_and_empty, comb]
  intro _
  bv_decide

/-! ### For comparison: the same assertion with SAT only, at this one depth -/

def InvSat (s : State) : Prop :=
  s.f_past_valid = 1#1 → s.count ≤ 4#3 ∧ s.wptr - s.rptr = s.count.extractLsb 1 0

theorem p_count_le_by_sat (s0 : State) (h0 : initOK s0) :
    (circuit s0).SafePrefix assumptions p_count_le := by
  refine safePrefix_of_inv _ _ _ InvSat ?_ ?_ ?_
  · intro h; simp only [initOK] at h0; simp only [circuit] at h; rw [h0] at h
    exact absurd h (by decide)
  · intro s i h hA; simp only [InvSat, assumptions, comb, circuit, step] at *; bv_decide
  · intro s i h _; simp only [InvSat, p_count_le, comb] at *; bv_decide

end Gen.Fifo4
