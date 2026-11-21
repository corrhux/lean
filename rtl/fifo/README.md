# fifo: synchronous FIFO, DEPTH = 2^AW (twin lab D5)

Pointers `rptr`, `wptr` (AW bits), occupancy `count` (AW+1 bits), memory
`mem[DEPTH]`. Pushing into a full FIFO and popping from an empty one are
ignored.

| Label | Meaning | Jasper equivalent |
|---|---|---|
| `p_count_le` | `count <= DEPTH` | `assert property (disable iff (rst) count <= DEPTH);` |
| `p_ptrs` | `wptr - rptr == count` (mod DEPTH) | the helper assertion that ties pointers to the counter |
| `p_not_full_and_empty` | never both full and empty | `assert property (!(full && empty));` |
| `c_full` | the FIFO can fill | `cover property (full);` |

## Lean side

| File | What |
|---|---|
| `RtlProof/Generated/Fifo4.lean` | generated at `AW=2, DW=4`; `sv2lean` maps the memory to registers `mem_0`…`mem_3` |
| `RtlProof/Examples/Fifo/Control.lean` | abstract control model with depth `2^aw` a **parameter**. `inv_step`: the invariant holds for **every** `aw`. Hand proof, no SAT. |
| `RtlProof/Examples/Fifo/Solution.lean` | `link`: one clock edge of the generated RTL = one abstract step at `aw = 2` (`bv_decide`). All three assertions are derived from the every-depth invariant. `p_count_le_by_sat` does it with SAT only, for comparison. |

Detail worth noticing: Yosys created a duplicate of the read pointer (`r_0`,
driving the read mux). The abstraction function `ctlOf` simply ignores it,
since the control properties don't need it. A data-integrity proof would have
to add the invariant `r_0 = rptr`.

## Measured

`ftwin run fifo`: every property is proven on both sides (SBY k-induction at
depth 4, and Lean).

`ftwin bench fifo` (k-induction per depth, `smtbmc z3`):

| AW (DEPTH) | 1 (2) | 2 (4) | 3 (8) | 4 (16) | 5 (32) |
|---|---|---|---|---|---|
| time | 1.1 s | 1.1 s | 1.1 s | 1.1 s | 1.2 s |
| Lean `inv_step` | one theorem, every AW | | | | |

Unlike the multiplier, these control properties are easy for the model checker
at every depth, **because the helper assertion `p_ptrs` makes them
inductive**. The difference here is not speed. It is that the model checker
needs one run per depth, while Lean states and proves the result for all
depths. Data integrity is the natural next step and is where checking each
depth separately gets expensive.

## Running

```sh
ftwin run fifo
ftwin bench fifo
sv2lean rtl/fifo/fifo.sv --top fifo -P AW=2 -P DW=4 --difftest 10
```
