import RtlProof.Core.Circuit

/-!
# Soundness of k-induction

The algorithm behind SymbiYosys `mode prove` (and the induction engines of
commercial tools), stated and proven as a theorem.

* **Base case:** BMC finds no violation in cycles `0 … k` from reset.
* **Inductive step:** from *any* state, if `P` holds for `k+1` consecutive
  cycles (`0 … k`), it also holds at cycle `k+1`.

Then `P` holds at every cycle. An *induction counterexample* is a start state
and input sequence that violates `hstep`. It is usually unreachable from
reset, which is why the step fails even though the property may be true. The
fixes are a larger `k` or a strengthened invariant (course chapter D3).
-/

namespace RtlProof.Circuit

variable {I S : Type}

/-- Running `m + j` cycles from reset = running `j` cycles from the state reached after `m`. -/
theorem run_add (c : Circuit I S) (ins : Nat → I) (m j : Nat) :
    c.run ins (m + j) = c.runFrom (c.run ins m) (fun t => ins (m + t)) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← Nat.add_assoc, run_succ, runFrom_succ, ih]

theorem kinduction_sound (c : Circuit I S) (P : S → Prop) (k : Nat)
    (hbase : c.BoundedSafe P k)
    (hstep : ∀ (s : S) (ins : Nat → I),
      (∀ j, j ≤ k → P (c.runFrom s ins j)) → P (c.runFrom s ins (k + 1))) :
    c.Safe P := by
  intro ins n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n ≤ k
    · exact hbase ins n hn
    · -- n = m + (k + 1): look back k+1 cycles to the state at cycle m
      obtain ⟨m, rfl⟩ : ∃ m, n = m + (k + 1) := ⟨n - (k + 1), by omega⟩
      rw [run_add]
      apply hstep
      intro j hj
      rw [← run_add]
      exact ih (m + j) (by omega)

/-- 1-induction is k-induction with `k = 0`. -/
theorem induction_of_kinduction (c : Circuit I S) (P : S → Prop)
    (h0 : P c.init) (hstep : ∀ s i, P s → P (c.step s i)) : c.Safe P :=
  kinduction_sound c P 0
    (fun _ n hn => by
      have : n = 0 := by omega
      subst this
      exact h0)
    (fun s ins h => hstep _ _ (h 0 (Nat.le_refl 0)))

end RtlProof.Circuit
