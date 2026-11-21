# arbiter: round-robin arbiter, N = 2^K requesters (twin lab D8)

`ptr` is the requester with priority this cycle. The grant goes to the first
requester at or after `ptr`, cyclically, and `ptr` then moves just past the
grant. There is no dynamic indexing: requests are rotated by `ptr`, the lowest
set bit is isolated (`x & -x`), then rotated back.

| Label | Meaning | Jasper equivalent |
|---|---|---|
| `p_onehot` | at most one grant | `assert property ($onehot0(gnt));` |
| `p_valid` | grants only to requesters | `assert property ((gnt & ~req) == 0);` |
| `p_work` | never idle while someone requests | `assert property (req != 0 -> gnt != 0);` |
| `p_fair` | requester `j` never waits N cycles in a row | symbolic index (`anyconst f_j`) + watchdog counter |
| `p_fair_helper` | `wait + dist(ptr → j) < N` | the helper assertion that makes induction work |
| `c_wait3` | j can actually wait 3 cycles (the worst case at N=4) | `cover property` |

`p_fair` is liveness turned into safety: "eventually granted" becomes "granted
within N cycles", which can be checked with a counter. `f_j` is a free
constant, so the check covers every requester at once.

## Lean side

| File | What |
|---|---|
| `RtlProof/Examples/Arbiter/Fairness.lean` | **Every N, no SAT.** `wait_inv_step`: the ranking argument (counter + distance stays below N). `rr_contract`: granting the least requesting offset makes a waiting requester strictly closer. |
| `RtlProof/Generated/Arbiter4.lean` | generated at K=2 (N=4); `f_j` becomes a register that never changes |
| `RtlProof/Examples/Arbiter/Solution.lean` | safety properties by one `bv_decide` each (they hold in every state); `p_fair` from the one width-specific fact `rtl_contract` plus the every-N ranking lemma |

## Measured

`ftwin run arbiter`: every property is proven on both sides.

k-induction (`smtbmc z3`) **with** the helper assertion: about 1.2 s for every
K from 1 to 4 (`ftwin bench arbiter`).

k-induction **without** the helper assertion:

| N (K) | depth 4 | depth 8 | depth 16 |
|---|---|---|---|
| 4 (2) | PASS | PASS | PASS |
| 8 (3) | **UNKNOWN** (induction step fails) | PASS | PASS |

Without the helper, the induction depth must grow with N, because the induction
step must look back far enough to rule out unreachable wait/pointer
combinations. The helper is exactly the invariant Lean proves once for every N
(`wait_inv_step`). Engines like IC3/PDR try to *discover* such invariants
automatically; in Lean you state it and the kernel checks it.

## Running

```sh
ftwin run arbiter
ftwin bench arbiter
sv2lean rtl/arbiter/arbiter.sv --top arbiter -P K=2 --difftest 10
```
