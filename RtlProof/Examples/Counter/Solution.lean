import RtlProof.Generated.Counter
import RtlProof.Meta.Induction
import Std.Tactic.BVDecide

/-!
# Counter twin: the Lean side (solution)

The model `Gen.Counter` is **generated** from `rtl/counter/counter.sv` by
`sv2lean`. This file proves the same assertions SymbiYosys checks (see
`rtl/counter/README.md`), for every cycle and every input sequence, under the
same assumption (`assume (rst)` in the first cycle).

| SymbiYosys task | Lean theorem |
|---|---|
| `prove` (k-induction) of `p_le_9` | `p_le_9_holds` |
| `prove` of `p_hold` | `p_hold_holds` |

Proof pattern for both: an inductive invariant (`safePrefix_of_inv`), with
each obligation discharged by `bv_decide` (a SAT call with a checked
certificate) after unfolding the generated definitions.
-/

namespace Gen.Counter
open RtlProof RtlProof.Circuit

/-- After the first cycle the counter stays in 0…9. Before it (`f_past_valid = 0`) nothing
is claimed: the reset assumption is what sets `cnt` to 0. -/
def Inv_le_9 (s : State) : Prop := s.f_past_valid = 1#1 → s.cnt ≤ 9#4

theorem p_le_9_holds (s0 : State) (h0 : initOK s0) :
    (circuit s0).SafePrefix assumptions p_le_9 := by
  refine safePrefix_of_inv _ _ _ Inv_le_9 ?_ ?_ ?_
  · -- initial state: f_past_valid = 0, so the invariant is vacuous
    intro h
    simp only [initOK] at h0
    simp only [circuit] at h
    rw [h0] at h
    exact absurd h (by decide)
  · -- one step preserves it, given the assumption in the current cycle
    intro s i hInv hA
    simp only [Inv_le_9, assumptions, comb, circuit, step] at *
    bv_decide
  · -- the invariant implies the assertion
    intro s i hInv _
    simp only [Inv_le_9, p_le_9, comb] at *
    bv_decide

/-- `p_hold` needs no assumption and no history beyond what its own registers store:
the registered copies `f_*_q` describe the previous cycle exactly. -/
def Inv_hold (s : State) : Prop :=
  s.f_past_valid = 1#1 → s.f_rst_q = 0#1 → s.f_en_q = 0#1 → s.cnt = s.f_cnt_q

theorem p_hold_holds (s0 : State) (h0 : initOK s0) :
    (circuit s0).SafePrefix assumptions p_hold := by
  refine safePrefix_of_inv _ _ _ Inv_hold ?_ ?_ ?_
  · intro h
    simp only [initOK] at h0
    simp only [circuit] at h
    rw [h0] at h
    exact absurd h (by decide)
  · intro s i _ _
    simp only [Inv_hold, comb, circuit, step]
    bv_decide
  · intro s i hInv _
    simp only [Inv_hold, p_hold, comb] at *
    bv_decide

end Gen.Counter
