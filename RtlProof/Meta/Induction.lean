import RtlProof.Core.Circuit

/-!
# Soundness of induction (what an induction engine relies on)

`induction_sound` is the theorem behind every unbounded "proven" from an
induction-based engine: if an invariant holds at reset, is preserved by every
transition, and implies the property, then the property holds at every cycle.

`bounded_of_safe` states the relationship between the two verdicts: a full
proof implies every bounded proof, but not the other way round.

k-induction soundness (`kinduction_sound`, ARCHITECTURE §4.1) is added at
milestone M1, once these files are compiled on the pinned toolchain.
-/

namespace RtlProof.Circuit

variable {I S : Type}

theorem induction_sound (c : Circuit I S) (P Inv : S → Prop)
    (h0 : Inv c.init)
    (hstep : ∀ s i, Inv s → Inv (c.step s i))
    (hP : ∀ s, Inv s → P s) :
    c.Safe P := by
  intro ins n
  apply hP
  induction n with
  | zero => exact h0
  | succ k ih =>
    rw [run_succ]
    exact hstep _ _ ih

theorem bounded_of_safe (c : Circuit I S) (P : S → Prop) (k : Nat) (h : c.Safe P) :
    c.BoundedSafe P k :=
  fun ins n _ => h ins n

end RtlProof.Circuit
