/-!
# Round-robin fairness, for every number of requesters (course D8)

Liveness ("every request is eventually granted") becomes a *bounded-wait*
safety property with a ranking function: the distance from the priority
pointer to the waiting requester. Two results, both for **every** `N`:

1. `wait_inv_step`: if each cycle in which requester `j` waits makes its
   distance strictly smaller, a waiting counter plus that distance stays below
   `N`. So `j` never waits `N` cycles in a row. This is the argument behind the
   RTL's helper assertion `p_fair_helper : f_wait + f_dist < N`.
2. `rr_contract`: an arbiter that grants the *first* requester at or after the
   pointer, and then moves the pointer just past the grant, satisfies that
   contract.

The RTL at `N = 4` is connected in `Solution.lean`. No SAT here: plain `Nat`
reasoning with `omega` and induction.
-/

namespace RtlProof.Arbiter

/-! ### 1. The ranking argument -/

/-- One cycle of the waiting counter: either the wait ends (counter back to 0), or `j`
keeps waiting, the counter grows by one and the distance shrinks. -/
theorem wait_inv_step {N wait dist wait' dist' : Nat}
    (hinv : wait + dist < N) (hdist' : dist' < N)
    (hstep : wait' = 0 ∨ (wait' = wait + 1 ∧ dist' < dist)) :
    wait' + dist' < N := by
  omega

/-- Hence the counter itself never reaches `N`. -/
theorem wait_lt {N wait dist : Nat} (h : wait + dist < N) : wait < N := by omega

/-! ### 2. Round-robin priority implies the contract

Requests are viewed *relative to the pointer*: `r k` means the requester at
offset `k` after the pointer is requesting. The grant goes to the least
requesting offset. -/

/-- The least requesting offset among `0 … n-1`, if any. -/
def least (r : Nat → Bool) : Nat → Option Nat
  | 0     => none
  | n + 1 =>
    match least r n with
    | some k => some k
    | none   => if r n then some n else none

theorem least_spec (r : Nat → Bool) (n k : Nat) (h : least r n = some k) :
    k < n ∧ r k = true ∧ ∀ m, m < k → r m = false := by
  induction n generalizing k with
  | zero => simp [least] at h
  | succ n ih =>
    simp only [least] at h
    split at h
    · rename_i k' hk'
      obtain ⟨h1, h2, h3⟩ := ih k' hk'
      cases h
      exact ⟨by omega, h2, h3⟩
    · rename_i hnone
      split at h
      · rename_i hr
        cases h
        refine ⟨by omega, hr, ?_⟩
        intro m hm
        cases hrm : r m
        · rfl
        · -- some smaller offset was requesting, so `least r n` would not be `none`
          exfalso
          have : ∀ n m, m < n → r m = true → least r n ≠ none := by
            intro n
            induction n with
            | zero => intro m hm; omega
            | succ n ih2 =>
              intro m hm hrm2
              simp only [least]
              split
              · simp
              · rename_i hn
                by_cases hmn : m < n
                · exact absurd hn (ih2 m hmn hrm2)
                · have : m = n := by omega
                  subst this; simp [hrm2]
          exact this n m (by omega) hrm hnone
      · simp at h

/-- If the requester at offset `d < n` is requesting, a grant exists, at offset `≤ d`. -/
theorem least_exists (r : Nat → Bool) (n d : Nat) (hd : d < n) (hr : r d = true) :
    ∃ k, least r n = some k ∧ k ≤ d := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [least]
    by_cases hdn : d < n
    · obtain ⟨k, hk, hkd⟩ := ih hdn
      exact ⟨k, by simp [hk], hkd⟩
    · have : d = n := by omega
      subst this
      split
      · rename_i k hk
        exact ⟨k, rfl, Nat.le_of_lt (least_spec r d k hk).1⟩
      · exact ⟨d, by simp [hr], Nat.le_refl d⟩

/-- **The round-robin contract, for every `N`.** If the requester at offset `d` is
requesting and is not the one granted (offset `g`), then `g < d`, and after the
pointer moves to `g + 1` its new offset is `d - (g + 1)`: strictly smaller. -/
theorem rr_contract (r : Nat → Bool) (N d g : Nat) (hd : d < N) (hr : r d = true)
    (hg : least r N = some g) (hne : g ≠ d) :
    g < d ∧ d - (g + 1) < d := by
  obtain ⟨k, hk, hkd⟩ := least_exists r N d hd hr
  rw [hg] at hk
  cases hk
  omega

end RtlProof.Arbiter
