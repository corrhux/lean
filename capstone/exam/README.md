# Ibex exam

The rest of Ibex, proved by you: the iterative multiplier/divider
(`ibex_multdiv_slow`) and the load/store unit (`ibex_load_store_unit`), both
translated unmodified from lowRISC Ibex. Prepare with the exam prep chapters
E5–E11 in [docs/CAPSTONE_EXAM_PREP.md](../../docs/CAPSTONE_EXAM_PREP.md).

| Item | Points | What you prove |
|---|---|---|
| M1 | 10 | Ibex's assertion `IbexMultDivStateValid` holds in every reachable state |
| M2 | 15 | a multiply raises `valid_o` exactly in cycle 32 |
| M3 | 10 | a divide raises it exactly in cycle 36 |
| M4 | 20 | with `data_ind_timing_i`, timing does not depend on the operands (`SEC_CM: CORE.DATA_REG_SW.SCA`) |
| L1 | 5 | a bus request is held until it is granted |
| L2 | 15 | in every reachable state, a store writes exactly the bytes SB/SH/SW write |
| L3 | 15 | a load returns the ISA's value however many cycles memory takes |
| L4 | 10 | a misaligned LW becomes two bus transactions and still returns the ISA's value |
| challenge | – | the multiplier, wired to the ALU's adder, computes `a * b` (open: no reference proof) |

## Files

| File | |
|---|---|
| `RtlProof/Exam/Ibex/MultDiv.lean`, `LoadStore.lean` | **yours**: replace each `sorry` |
| `RtlProof/Exam/Ibex/Statements.lean` | the statements (do not edit) |
| `RtlProof/Exam/Ibex/Spec.lean` | the definitions they use: FSM encodings, the ISA's load and store, the composed multiplier (do not edit) |
| `RtlProof/Generated/IbexMD.lean`, `IbexLSU.lean` | the models, from `capstone/ibex/generate.sh` (difftested against Yosys) |
| `capstone/exam/simcheck.lean` | evidence for the challenge statement: 400 random cases |
| `capstone/exam/solutions/` | **reference solutions: spoilers**. CI grades them to keep every statement provable. The tutor will not read them. |

## Grading

```sh
pvs-exam                  # your files
pvs-exam --json r.json    # and as JSON
```

or the web app's **Ibex exam** view (`pvs-app`), which also gives you a live Lean
editor with the goal at the cursor. An item scores when your theorem has exactly the
exam's statement and its proof relies only on Lean's kernel and `bv_decide`. Edits to
the protected files (`capstone/exam/protected.sha256`) make the result unofficial.

## How long it takes

The reference solutions are under 300 lines, and each `bv_decide` call takes
seconds. Expect M1 and L1 to take minutes once E5 and E6 make sense, and the rest
to take hours. M4 and L2 are the ones that teach the most.
