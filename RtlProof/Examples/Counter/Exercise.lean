import RtlProof.Generated.Counter
import RtlProof.Meta.Induction
import Std.Tactic.BVDecide

/-!
# Counter twin: exercise

Prove the two assertions of `rtl/counter/counter.sv` on the generated model
`Gen.Counter` (open `RtlProof/Generated/Counter.lean` next to this file).
Replace each `sorry`. Solution: `Solution.lean` in this folder.

The Jasper view: you are writing the *helper assertion* (`Inv_…`) that
makes induction succeed, then discharging each obligation with a SAT call
(`bv_decide`).

Hints, in order of strength:
1. `refine safePrefix_of_inv _ _ _ YourInvariant ?_ ?_ ?_` leaves three goals:
   initial state, one step, invariant ⇒ assertion.
2. The generated definitions must be unfolded before `bv_decide` can see the
   bit-vectors: `simp only [assumptions, comb, circuit, step, p_le_9] at *`.
3. If `bv_decide` reports a counterexample in the step goal, read it like an
   induction CEX: is that state reachable? If not, strengthen the invariant.
4. For `p_le_9`, the invariant needs to say nothing about the very first
   cycle. Why? Look at `initOK` and `assumptions`.
-/

namespace Gen.Counter
open RtlProof RtlProof.Circuit

theorem p_le_9_holds' (s0 : State) (h0 : initOK s0) :
    (circuit s0).SafePrefix assumptions p_le_9 := by
  sorry

theorem p_hold_holds' (s0 : State) (h0 : initOK s0) :
    (circuit s0).SafePrefix assumptions p_hold := by
  sorry

end Gen.Counter
