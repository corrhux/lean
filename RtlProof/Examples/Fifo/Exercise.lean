import RtlProof.Examples.Fifo.Control

/-!
# FIFO twin: exercise

The abstract control model and its invariant are in `Control.lean`. Re-prove
the push and pop transitions for **every** depth `2 ^ aw`. The helper lemmas
`toNat_succ`, `toNat_pred`, `setWidth_sub'` and `setWidth_one'` are available.

Hints:
1. Split the invariant with `obtain ⟨hc, hp⟩ := h` and the goal with `refine ⟨?_, ?_⟩`.
2. Counter bound: rewrite with `toNat_succ`/`toNat_pred`, then `omega`.
3. Pointer equation: push `setWidth` through `+`/`-` (`BitVec.setWidth_add`,
   `setWidth_sub'`), then rearrange with `BitVec.add_assoc`, `BitVec.add_comm`,
   `BitVec.sub_add_cancel`.
-/

namespace RtlProof.Fifo
variable {aw : Nat}

theorem inv_push'' (s : Ctl aw) (h : Inv s) (hf : s.count.toNat ≠ 2 ^ aw) :
    Inv ⟨s.rptr, s.wptr + 1, s.count + 1⟩ := by
  sorry

theorem inv_pop'' (s : Ctl aw) (h : Inv s) (he : s.count.toNat ≠ 0) :
    Inv ⟨s.rptr + 1, s.wptr, s.count - 1⟩ := by
  sorry

end RtlProof.Fifo
