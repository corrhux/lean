# mul: shift-and-add array multiplier (twin lab D6)

`p = a * b` at width `W` (wrapping), built as `acc[i+1] = acc[i] + (b[i] ? a << i : 0)`.
One assertion: `p_mul : p == a * b`. Jasper: `assert property (p == a * b);`, a
combinational check, so a 1-step BMC is already a complete proof.

## The point of this lab

| Approach | What it proves | Cost as `W` grows |
|---|---|---|
| SymbiYosys (smtbmc + Z3) | `p == a*b` at **one** `W` | grows steeply (table below) |
| Lean `bv_decide` on the generated model | `p == a*b` at **one** `W` | also grows steeply: it is SAT too |
| Lean induction (`RtlProof.Mul.acc_eq_mul`) | the shift-and-add algorithm equals `*` for **every** `W` | one proof, 0.3 s to check, no SAT |
| Lean link lemma (`Gen.Mul8.rtl_is_acc`) | the generated RTL *is* that algorithm at one `W` | grows much more slowly than the arithmetic check |

`acc_eq_mul` reuses Lean core's `BitVec.mulRec_eq_mul_signExtend_setWidth`:
the same shift-and-add recurrence `bv_decide` uses to bit-blast `*`, proven
correct for every width in Lean's own library.

## Measured (4-core cloud VM; times vary by machine)

SymbiYosys, `mode bmc`, `depth 1`, `smtbmc z3` (`ftwin bench mul`):

| W | 4 | 6 | 8 | 10 | 12 |
|---|---|---|---|---|---|
| time | 1.0 s | 1.0 s | 1.3 s | 5.1 s | 25 s |

Lean on the generated model:

| W | direct `bv_decide` on `p == a*b` | link lemma (`bv_decide`) + `acc_eq_mul` |
|---|---|---|
| 8 | 2.9 s | 1.0 s |
| 12 | **gave up** after 443 s (Lean's default step budget) | 5.4 s |
| 16 | still running after 30 min, stopped | 24.8 s |
| 32 | not attempted | **SAT timeout** at 600 s |

The all-widths theorem itself trusts only the kernel (`propext`,
`Classical.choice`, `Quot.sound`). The RTL-level theorem `p_mul_holds` adds a
`bv_decide` axiom, for the link lemma only.

## Honest limit

The link lemma is still a fixed-width SAT problem, because Yosys elaborates
one `W` at a time (ADR-4 in docs/ARCHITECTURE.md). It is much cheaper than the
arithmetic check, since both sides have the same structure, but it still
grows: at 32 bits even the link times out. A fully width-free result needs the RTL itself modelled parametrically
in Lean. That is course chapter D5's hand-written parametric model, which the
FIFO lab does for its control logic.

## Running

```sh
ftwin run mul                  # SBY at W=4, 8 and Lean (W=8 model + all-widths theorem)
ftwin bench mul                # SBY sweep over W next to the one Lean theorem
sv2lean rtl/mul/mul.sv --top mul -P W=8 --difftest 10
```
