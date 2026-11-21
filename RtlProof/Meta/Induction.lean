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

/-- Induction with assumptions (the form used on `sv2lean` models): an invariant that
holds initially and is preserved by every step *whose inputs satisfy the assumptions*,
and that implies the property, proves the property under model-checker (prefix)
semantics. In Jasper terms, `Inv` is the helper assertion that makes the proof go
through. -/
theorem safePrefix_of_inv (c : Circuit I S) (A P : S → I → Prop) (Inv : S → Prop)
    (h0 : Inv c.init)
    (hstep : ∀ s i, Inv s → A s i → Inv (c.step s i))
    (hP : ∀ s i, Inv s → A s i → P s i) :
    c.SafePrefix A P := by
  intro ins n hA
  have hInv : ∀ m, m ≤ n → Inv (c.run ins m) := by
    intro m
    induction m with
    | zero => intro _; exact h0
    | succ k ih =>
      intro hk
      rw [run_succ]
      exact hstep _ _ (ih (by omega)) (hA k (by omega))
  exact hP _ _ (hInv n (Nat.le_refl n)) (hA n (Nat.le_refl n))

theorem bounded_of_safe (c : Circuit I S) (P : S → Prop) (k : Nat) (h : c.Safe P) :
    c.BoundedSafe P k :=
  fun ins n _ => h ins n

end RtlProof.Circuit
