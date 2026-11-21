import RtlProof.Examples.Mul.Solution

/-!
# Multiplier twin: exercise

Prove that the shift-and-add algorithm computes `*` for **every** width. The
definitions are in `Solution.lean` (`RtlProof.Mul.acc`).

Hints, in order of strength:
1. Relate `acc a b (k+1)` to Lean core's `BitVec.mulRec a b k` by induction on `k`.
   Use `#check @BitVec.mulRec_succ_eq`.
2. Core proves `BitVec.mulRec_eq_mul_signExtend_setWidth`. What does
   `setWidth w` do when the width doesn't change? (`BitVec.setWidth_eq`)
3. Width 0 is special: every `BitVec 0` equals every other.
   (`BitVec.eq_of_getLsbD_eq`)
-/

namespace RtlProof.Mul

theorem acc_succ_eq_mulRec' {w : Nat} (a b : BitVec w) (k : Nat) :
    acc a b (k + 1) = BitVec.mulRec a b k := by
  sorry

theorem acc_eq_mul' {w : Nat} (a b : BitVec w) : acc a b w = a * b := by
  sorry

end RtlProof.Mul
