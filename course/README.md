# Proof vs. Search: the course, chapter by chapter

Work through the parts in order. For each chapter: **read** the listed
section, **do** the lab, then compare with the **files**. Exercises have a
`Solution.lean` next to them. When stuck, use `tutor` (needs an API key) or
the hints at the top of each exercise.

Setup (once): open the repository in the dev container (`.devcontainer/`), or

```sh
pip install -e ".[dev,hdl]"     # satlab, sv2lean, ftwin, WebAssembly Yosys/SymbiYosys
lake build                      # the Lean library (needs elan)
git submodule update --init     # lowRISC Ibex, for Part E
```

The syllabus with learning objectives is [docs/COURSE.md](../docs/COURSE.md).

**In the app** (`./start`), each chapter's "Do" column maps to one view:

| Command in the table | In the app |
|---|---|
| `ftwin run <design>`, `ftwin bench <design>` | Twin labs → pick the design → Run both sides / Benchmark |
| editing `Exercise.lean`, typing LEAN_FLUENCY examples | Lean workbook → pick the exercise, or the scratchpad |
| satlab Labs 1–5 (`satlab gen/solve/trace/ablate/check`) | SAT lab → Labs |
| `satlab zoo` | SAT lab → Solver zoo |
| `pvs-exam` | Ibex exam → Save and grade |

A few steps stay in a terminal: `sv2lean --difftest`, `capstone/ibex/generate.sh`, and
the Jasper practical (E10).

---

## Part A: Orientation

| Ch. | Read | Do | Files |
|---|---|---|---|
| A0 Two ways to be sure | COURSE.md § A0 (the Jasper ⇄ Lean table) | `ftwin run counter`: BMC, k-induction and a Lean proof of the same assertion, side by side | `rtl/counter/`, `RtlProof/Examples/Counter/` |

## Part B: What runs under the hood of Jasper

| Ch. | Read | Do | Files |
|---|---|---|---|
| B1 RTL to CNF | COURSE.md § B1 | `satlab gen add-miter --width 8 -o a.cnf`; `satlab gen mul-miter --width 8 -o m.cnf`: compare their sizes | `satlab/cnf.py` (Tseitin, bit-blasted adders and multipliers) |
| B2 DPLL to CDCL | COURSE.md § B2 | satlab Lab 1 (watch CDCL learn) and `satlab ablate m.cnf` | `satlab/dpll.py`, `satlab/cdcl.py`, [satlab/README.md](../satlab/README.md) |
| B3 Solver family tree | COURSE.md § B3 | `satlab zoo m.cnf` at widths 8 and 10; satlab Labs 3 and 4 | `satlab/zoo.py` |
| B4 Inside a model checker | COURSE.md § B4 | satlab Lab 2 (a counterexample from a SAT model); `cd rtl/counter && yowasp-sby … counter.sby bmc prove` | `satlab/gen.py` (`counter_bmc`), `RtlProof/Meta/KInduction.lean` |
| B5 Certificates | COURSE.md § B5 | satlab Lab 5 (`--proof`, `satlab check`) | `satlab/certs.py` |
| B6 SAT inside a prover | COURSE.md § B6; LEAN_FLUENCY.md § L13 | Prove `x ^^^ y ^^^ y = x` with `bv_decide`, then `#print axioms` | `docs/LEAN_FLUENCY.md` L13 |
| B7 History | COURSE.md § B7 | (reading) | `docs/REFERENCES.md` |

## Part C: Lean fluency

[docs/LEAN_FLUENCY.md](../docs/LEAN_FLUENCY.md), lessons L0–L17. Type every
example into a scratch file starting with `import Std.Tactic.BVDecide`. All
48 code blocks are checked in CI, so they work as written.

| Block | Lessons | Exit check |
|---|---|---|
| C1 The language | L0–L5 | drills L1–L5 |
| C2 Logic and proof | L6–L8 | drills L6–L8 |
| C3 Tactics | L9–L13 | drills L9–L13 |
| C4 Putting it together | L14–L17 | drills L14; then `RtlProof/Examples/Counter/Exercise.lean` without hints |

## Part D: Twin labs

Each lab has a design README (properties with their Jasper SVA, measured
results), an exercise and a solution. `ftwin run <design>` shows both sides;
`ftwin bench <design>` sweeps the parameter.

| Ch. | Design | Read | Exercise | Key result |
|---|---|---|---|---|
| D1–D3 Modelling, safety, invariants | counter | [rtl/counter/README.md](../rtl/counter/README.md) | `RtlProof/Examples/Counter/Exercise.lean` | the bug variant's induction counterexample is one transition, not a trace |
| D4 SAT inside the prover | (all) | LEAN_FLUENCY.md L13 | — | `#print axioms` shows what `bv_decide` adds to the trust base |
| D5 Parameterized | fifo | [rtl/fifo/README.md](../rtl/fifo/README.md) | `RtlProof/Examples/Fifo/Exercise.lean` | control invariant for **every** depth; one model-checker run per depth |
| D6 Datapath | mul | [rtl/mul/README.md](../rtl/mul/README.md) | `RtlProof/Examples/Mul/Exercise.lean` | SAT time explodes with width; one proof covers every width |
| D7 Equivalence & refinement | fifo, mul | the `link` lemmas in both solutions | — | a generated netlist refines a hand-written parametric model |
| D8 Liveness & fairness | arbiter | [rtl/arbiter/README.md](../rtl/arbiter/README.md) | `RtlProof/Examples/Arbiter/Exercise.lean` | ranking argument for every N; k-induction needs depth ≈ N without the helper |
| D9 Assumptions | counter, fifo | `SafePrefix` in `RtlProof/Core/Circuit.lean`; `safePrefix_of_inv` | — | the model checker's "assumption prefix" semantics, as a definition |
| D10 Crossing the gap | — | CAPSTONE_PRIMER.md § 7 | — | lemma structure is what makes industrial proofs converge |

## Part E: Capstone, lowRISC Ibex

Read [docs/CAPSTONE_PRIMER.md](../docs/CAPSTONE_PRIMER.md) first, then
[capstone/ibex/README.md](../capstone/ibex/README.md).

| Ch. | Read | Do | Files |
|---|---|---|---|
| E0 The verification target | CAPSTONE_PRIMER.md §§ 1–8 | Answer the § 7.3 questions using `third_party/ibex/dv/formal/` | `third_party/ibex/` |
| E1 Meet Ibex | CAPSTONE_IBEX.md §§ 1–3 | `capstone/ibex/generate.sh --difftest`: four Ibex blocks translated to Lean and checked against Yosys | `RtlProof/Generated/Ibex*.lean` |
| E2 Track 1: model checking | CAPSTONE_IBEX.md § 4 Track 1 | needs the native OSS CAD Suite (dev container): riscv-formal and the Sail-equivalence flow | `third_party/ibex/formal/`, `third_party/ibex/dv/formal/` |
| E3 Track 2: Lean on blocks | capstone/ibex/README.md | Read the spec (`RtlProof/RV32I/Spec.lean`, `Compressed.lean`), then each proof; break the spec on purpose and read `bv_decide`'s counterexample | `RtlProof/RV32I/Ibex/*.lean` |
| E4 Track 3: pipeline slice | CAPSTONE_IBEX.md § 4 Track 3 | open research step: see E11 and "Not done yet" in the capstone README | — |
| E5 Reading a generated model | CAPSTONE_EXAM_PREP.md § E5 | Check the asynchronous-reset and packing examples; find `md_state_q_ff` and `md_state_q` in `IbexMD.lean` | `RtlProof/Generated/IbexMD.lean`, `IbexLSU.lean` |
| E6 One-step rules and invariants | § E6 | Run the failing block, read the unreachable counterexample, then the fixed invariant | `docs/CAPSTONE_EXAM_PREP.md` |
| E7 Counting cycles | § E7 | The countdown proof: one step in `BitVec`, the induction in `Nat` | " |
| E8 Two runs | § E8 | The leaking and the fixed divider: read the counterexample to non-interference | " |
| E9 Refinement and composition | § E9 | Memory-semantic store spec; the nibble adder; run the composed multiplier | `RtlProof/Exam/Ibex/Spec.lean` |
| E10 Track 1 practical | § E10 | On your own machine with Jasper (or Yosys + rIC3): Ibex vs. Sail | `third_party/ibex/dv/formal/` |
| E11 Track 3 outline | § E11 | (reading) | — |
| **Exam** | [capstone/exam/README.md](../capstone/exam/README.md) | Prove M1–M4 and L1–L4 (100 points), optionally the challenge; grade with `pvs-exam` or the web app's Exam view | `RtlProof/Exam/Ibex/MultDiv.lean`, `LoadStore.lean` |
| E12 Retrospective | CAPSTONE_PRIMER.md § 8 (coverage matrix) | Write your own comparison: what each method found, what it cost, what it trusts | — |
