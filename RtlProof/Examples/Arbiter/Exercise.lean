import RtlProof.Examples.Arbiter.Fairness

/-!
# Arbiter twin: exercise

Two proofs that hold for **every** number of requesters `N`.

1. The ranking argument. (Hint: it's pure arithmetic; read the hypotheses
   aloud, then try `omega`.)
2. Round-robin priority implies the contract. Use `least_exists` to get a
   grant at offset `≤ d`, compare it with `hg`, and finish with `omega`.

Then open `Solution.lean` and see how the RTL at `N = 4` needs only one
width-specific fact, `rtl_contract`.
-/

namespace RtlProof.Arbiter

theorem wait_inv_step' {N wait dist wait' dist' : Nat}
    (hinv : wait + dist < N) (hdist' : dist' < N)
    (hstep : wait' = 0 ∨ (wait' = wait + 1 ∧ dist' < dist)) :
    wait' + dist' < N := by
  sorry

theorem rr_contract' (r : Nat → Bool) (N d g : Nat) (hd : d < N) (hr : r d = true)
    (hg : least r N = some g) (hne : g ≠ d) :
    g < d ∧ d - (g + 1) < d := by
  sorry

end RtlProof.Arbiter
