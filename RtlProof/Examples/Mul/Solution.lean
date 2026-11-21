import RtlProof.Generated.Mul8
import Std.Tactic.BVDecide

/-!
# Multiplier twin (course D6): search vs. proof

`rtl/mul/mul.sv` is a shift-and-add array multiplier with parameter `W` and one
assertion, `p_mul : p == a * b`.

* **Model checking / SAT** proves it one width at a time, and the cost explodes
  with `W` (see `rtl/mul/README.md` for measured times).
* **Lean** proves the *algorithm* correct once, for every width
  (`acc_eq_mul`), by induction and no search. The width-specific part shrinks
  to a *link lemma*: the generated RTL model computes exactly that algorithm.
  The link is structural and stays cheap for `bv_decide`, unlike the
  arithmetic fact itself.
-/

namespace RtlProof.Mul

/-- The RTL's algorithm at any width: `acc 0 = 0`, `acc (k+1) = acc k + (b[k] ? a << k : 0)`. -/
def acc {w : Nat} (a b : BitVec w) : Nat → BitVec w
  | 0     => 0
  | k + 1 => acc a b k + (if b.getLsbD k then a <<< k else 0)

/-- Our accumulator is Lean core's `BitVec.mulRec`, the shift-and-add recurrence
that `bv_decide` itself uses to bit-blast `*`. -/
theorem acc_succ_eq_mulRec {w : Nat} (a b : BitVec w) (k : Nat) :
    acc a b (k + 1) = BitVec.mulRec a b k := by
  induction k with
  | zero => simp [acc, BitVec.mulRec_zero_eq]
  | succ k ih => rw [acc, ih, BitVec.mulRec_succ_eq]

/-- **The array multiplier is correct for every width `w`.** No SAT, no native code:
`#print axioms` shows only Lean's three standard axioms. -/
theorem acc_eq_mul {w : Nat} (a b : BitVec w) : acc a b w = a * b := by
  cases w with
  | zero => exact BitVec.eq_of_getLsbD_eq (fun _ hi => absurd hi (by omega))
  | succ n =>
    rw [acc_succ_eq_mulRec, BitVec.mulRec_eq_mul_signExtend_setWidth, BitVec.setWidth_eq,
        BitVec.setWidth_eq]

end RtlProof.Mul

namespace Gen.Mul8
open RtlProof.Mul

/-- Link lemma: the generated W=8 netlist computes `acc` at width 8. Both sides have the
same shift-and-add structure, so this SAT problem is easy. -/
theorem rtl_is_acc (s : State) (i : Input) : (comb s i).p = acc i.a i.b 8 := by
  simp only [comb, acc]
  bv_decide

/-- The SVA assertion `p_mul`, from the link lemma plus the all-widths theorem. -/
theorem p_mul_holds (s : State) (i : Input) : p_mul s i := by
  intro _
  have h := rtl_is_acc s i
  rw [acc_eq_mul] at h
  simp only [comb] at h ⊢
  rw [h]
  simp

/-- The same assertion by brute-force SAT, for comparison. Fine at 8 bits; at 12 bits
it exhausts Lean's default budget after several minutes (see rtl/mul/README.md). -/
theorem p_mul_holds_by_sat (s : State) (i : Input) : p_mul s i := by
  simp only [p_mul, comb]
  bv_decide

end Gen.Mul8
