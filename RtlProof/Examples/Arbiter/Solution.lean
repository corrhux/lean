import RtlProof.Generated.Arbiter4
import RtlProof.Examples.Arbiter.Fairness
import RtlProof.Meta.Induction
import Std.Tactic.BVDecide

/-!
# Arbiter twin (course D8): the RTL at `N = 4`

`Gen.Arbiter4` is generated from `rtl/arbiter/arbiter.sv` with `K = 2`.
`f_j` is the free constant (`anyconst`) that picks an arbitrary requester,
exactly as in the Jasper-style fairness check.

* `p_onehot`, `p_valid`, `p_work` hold in **every** state, so no invariant is
  needed: one `bv_decide` call each.
* `p_fair` (j never waits 4 cycles in a row) uses the ranking argument from
  `Fairness.lean`, which holds for every `N`. The only width-specific fact is
  `rtl_contract`: one clock edge either ends j's wait or moves the pointer
  strictly closer to j.
-/

namespace Gen.Arbiter4
open RtlProof RtlProof.Circuit

/-! ### Safety: true in every state -/

theorem p_onehot_holds (s0 : State) : (circuit s0).SafePrefix assumptions p_onehot :=
  safePrefix_of_inv _ _ _ (fun _ => True) trivial (fun _ _ _ _ => trivial)
    (fun s i _ _ => by simp only [p_onehot, comb]; bv_decide)

theorem p_valid_holds (s0 : State) : (circuit s0).SafePrefix assumptions p_valid :=
  safePrefix_of_inv _ _ _ (fun _ => True) trivial (fun _ _ _ _ => trivial)
    (fun s i _ _ => by simp only [p_valid, comb]; bv_decide)

theorem p_work_holds (s0 : State) : (circuit s0).SafePrefix assumptions p_work :=
  safePrefix_of_inv _ _ _ (fun _ => True) trivial (fun _ _ _ _ => trivial)
    (fun s i _ _ => by simp only [p_work, comb]; bv_decide)

/-! ### Fairness -/

/-- Distance from the priority pointer to the tracked requester `j`. -/
def dist (s : State) : Nat := (s.f_j - s.ptr).toNat

/-- **The RTL's round-robin contract** (the one width-specific fact): after one clock
edge, either j's wait counter is back to 0, or it grew by one and j got strictly closer
to the pointer. -/
theorem rtl_contract (s : State) (i : Input) (hw : s.f_wait.toNat < 4) :
    (step s i).f_wait.toNat = 0 ∨
      ((step s i).f_wait.toNat = s.f_wait.toNat + 1 ∧ dist (step s i) < dist s) := by
  have h : (step s i).f_wait = 0#3 ∨
      ((step s i).f_wait = s.f_wait + 1#3 ∧ s.f_j - (step s i).ptr < s.f_j - s.ptr) := by
    simp only [step, comb]
    bv_decide
  have hj : (step s i).f_j = s.f_j := rfl
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl (by rw [h]; rfl)
  · refine Or.inr ⟨?_, ?_⟩
    · rw [h1, BitVec.toNat_add]; simp; omega
    · simp only [dist, hj]; exact h2

/-- The helper invariant (the RTL's `p_fair_helper`): after reset, `wait + dist < 4`. -/
def InvFair (s : State) : Prop := s.f_past_valid = 1#1 → s.f_wait.toNat + dist s < 4

theorem invFair_step (s : State) (i : Input) (hI : InvFair s) (hA : assumptions s i) :
    InvFair (step s i) := by
  intro _
  have hd' : dist (step s i) < 4 := (step s i).f_j - (step s i).ptr |>.isLt
  by_cases hv : s.f_past_valid = 1#1
  · have hinv := hI hv
    have := rtl_contract s i (by omega)
    exact RtlProof.Arbiter.wait_inv_step hinv hd' this
  · -- first cycle: the assumption forces reset, which clears the wait counter
    have h0 : (step s i).f_wait = 0#3 := by
      simp only [assumptions, comb] at hA
      simp only [step, comb]
      bv_decide
    rw [h0]; simpa using hd'

theorem p_fair_holds (s0 : State) (h0 : initOK s0) :
    (circuit s0).SafePrefix assumptions p_fair := by
  refine safePrefix_of_inv _ _ _ InvFair ?_ invFair_step ?_
  · intro h; simp only [initOK] at h0; simp only [circuit] at h; rw [h0] at h
    exact absurd h (by decide)
  · intro s i hI _
    simp only [p_fair, comb]
    intro hv
    have hlt : s.f_wait.toNat < 4 := RtlProof.Arbiter.wait_lt (hI (by bv_decide))
    have : s.f_wait < 4#3 := by rw [BitVec.lt_def]; simpa using hlt
    bv_decide

end Gen.Arbiter4
