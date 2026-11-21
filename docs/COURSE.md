# Proof vs. Search — Course Syllabus

Audience: an expert Jasper/FPV user learning Lean 4. Each chapter has
**Objectives · Reading · Lab · Jasper mapping · Debrief** ("what changed vs.
model checking"). Lab ids refer to `rtl/`, `RtlProof/Examples/`, `satlab/`.

Citations in this file are short-form; full entries and links are in
[REFERENCES.md](REFERENCES.md). Dates and attributions marked † are to be
re-verified against the primary source while writing the chapter.

---

## Part A — Orientation

### A0. Two ways to be sure
- **Objectives:** state precisely what "proven" means for (a) a model-checking
  engine and (b) a proof checked by a small kernel; know where each wins.
- **Content:** the Rosetta table (below); search vs. construction; complete
  automation on finite problems vs. human-guided proofs over infinite domains.
- **Lab:** `counter` — Jasper-style `prove` with BMC, k-induction and PDR; then
  the same property proved in Lean in three lines. Compare outputs side by side.

| Jasper / SAT-based MC | Lean 4 |
|---|---|
| `assert property` | theorem `Safe c P` |
| `assume property` | hypothesis (`SafeUnder c A P`) |
| `cover property` | existential theorem `∃ ins n, Q (run c ins n)` (witness = trace) |
| Engine K / BMC, bounded proof to depth N | `BoundedSafe c P N` — a *different, weaker theorem* |
| PDR/IC3 finds invariant automatically | you state `Inv`; Lean checks it |
| Helper assertion / assume-guarantee | lemma; lemma composition |
| Induction CEX (unreachable start state) | unprovable inductive step goal |
| Elaborated WIDTH=32 | `∀ n : Nat` (all widths at once) |
| Cutpoint / black box / abstraction | refinement / simulation relation |
| SEC app | refinement proof vs. functional spec |
| `s_eventually` + fairness | ranking function / well-founded measure |
| Trust: engine implementation | Trust: kernel (+ LRAT checker for `bv_decide`) |
| CEX waveform | open goal state, or `bv_decide` counterexample |

---

## Part B — What runs under the hood of Jasper (SAT, SMT, and proofs)

### B1. From RTL to CNF
- **Objectives:** bit-blast a word-level circuit; explain AIGs and Tseitin;
  read a DIMACS file.
- **Content:** Boolean satisfiability; CNF; Tseitin encoding (linear size,
  equisatisfiable); And-Inverter Graphs (AIGs) as the lingua franca of hardware
  MC (AIGER format); structural hashing; how a 32-bit adder and a 32-bit
  multiplier look as CNF (and why the multiplier is so much harder).
- **Lab:** `satlab/gen` — export `adder` and `multiplier` at widths 4/8/16 to
  AIGER and CNF; count variables/clauses.

### B2. DPLL → CDCL: how a modern solver actually searches
- **Objectives:** trace a CDCL run by hand; explain each core technique and what it buys.
- **Content:**
  - DPLL (Davis–Putnam–Logemann–Loveland, 1960–62): decide, unit propagate, backtrack.
  - **CDCL** (GRASP, 1996): conflict analysis on the implication graph,
    **1UIP** learned clauses, **non-chronological backjumping**.
  - **Two watched literals** and **VSIDS** branching (Chaff, 2001).
  - **Restarts** (Luby; glucose-style dynamic), **phase saving**.
  - **Clause database reduction** by LBD ("glue", Glucose, 2009).
  - Learned-clause minimisation; preprocessing (bounded variable elimination,
    SatELite 2005) and **inprocessing** (vivification, subsumption, probing).
- **Lab:** `satlab/cdcl.py` step-through on a 3-frame BMC of `counter`;
  toggle VSIDS/restarts/phase-saving and watch conflict counts change.

### B3. The solver family tree — how solvers really differ
- **Objectives:** explain *why* two correct solvers can differ by 100× on the
  same instance; choose a solver for a job.
- **Content — lineage and signature ideas:**

| Solver | Year† | Signature contribution |
|---|---|---|
| GRASP | 1996 | Conflict-driven learning, non-chronological backtracking |
| Chaff / zChaff | 2001 | Two watched literals, VSIDS, cheap restarts |
| MiniSat | 2003– | Small, clean, hackable reference design; **incremental assumptions API**; became the base of countless tools |
| Glucose | 2009– | LBD measure for learned-clause quality; aggressive DB reduction |
| CryptoMiniSat | 2009– | Native XOR clauses + Gaussian elimination (crypto/parity-heavy) |
| Lingeling / Plingeling / Treengeling | 2010– | Heavy inprocessing; parallel/cube-and-conquer variants |
| MapleSAT family | 2016– | Learning-rate-based branching (LRB) |
| CaDiCaL | 2017– | Readable modern CDCL, strong inprocessing, **proof output (DRAT/LRAT)**, incremental API; ships inside Lean's `bv_decide` |
| Kissat | 2020– | CaDiCaL ideas re-engineered in C for speed; repeated SAT Competition winner |
| ABC's internal solvers | — | Tuned for AIG-derived instances, deeply integrated with `pdr`, `bmc3`, sweeping |

  - What actually differs: branching heuristic, restart policy, DB reduction,
    pre/inprocessing, data-structure engineering, special reasoning (XOR,
    cardinality), parallel/portfolio strategy, incremental-API quality, proof output.
  - **No solver dominates**: SAT Competition results; portfolio solving; why
    Jasper (and ABC's `dprove`/`&` scripts) run engine *portfolios*.
  - **SMT** and DPLL(T): theory solvers; **bit-vector** solving — eager
    bit-blasting vs. word-level reasoning (Boolector, Bitwuzla), plus Z3, cvc5,
    Yices; arrays for memories; why `smtbmc` with Bitwuzla can beat pure SAT on
    datapath-heavy designs.
  - **On commercial engines:** Jasper's internals are proprietary; this chapter
    teaches the *families of technique* such engines draw on, without claiming
    what any specific Jasper engine contains.
- **Lab:** `satlab/zoo.py` — run MiniSat, Glucose, CaDiCaL, Kissat, Lingeling,
  Bitwuzla, Z3 on: adder miter, multiplier miter (w = 8…16), pigeonhole(n),
  BMC of `fifo`. Produce the comparison table; explain each outlier.

### B4. Inside a model checker
- **Objectives:** connect each Jasper engine class to an algorithm.
- **Content:** BMC (Biere, Cimatti, Clarke, Zhu 1999) as one SAT call per depth;
  **incremental SAT with assumptions** to reuse learned clauses across depths;
  k-induction (Sheeran, Singh, Stålmarck 2000) and uniqueness constraints;
  Craig interpolation (McMillan 2003); **IC3/PDR** (Bradley 2011; Eén,
  Mishchenko, Brayton 2011) as *thousands of tiny incremental SAT queries*
  building relatively inductive clauses frame by frame; SAT sweeping / fraiging
  for equivalence (SEC); BDD-based MC as historical context (McMillan's SMV, 1992).
- **Lab:** `satlab/incremental.py` — mini-BMC and mini-IC3 on `counter`;
  compare with `abc pdr` and rIC3 logs; extract IC3's final invariant and
  **paste it into Lean as `Inv`** — the bridge to Part D.

### B5. Certificates: trusting a SAT/UNSAT answer
- **Objectives:** explain why SAT answers are self-certifying but UNSAT answers
  need proofs; read an LRAT proof.
- **Content:** a SAT model is checked in linear time; UNSAT requires a
  refutation: resolution proofs, RUP, **DRAT** (Wetzler, Heule, Hunt 2014),
  **LRAT** (Cruz-Filipe et al. 2017, hints make checking cheap), FRAT (2021);
  checkers drat-trim, lrat-check; **formally verified checkers** (cake_lpr in
  CakeML; ACL2's verified LRAT checker; Lean's checker inside `bv_decide`).
  Model-checker analogues: invariant certificates for IC3, witness checking
  (e.g. Certifaiger†), and why most FPV tools don't emit them.
- **Lab:** `satlab/certs.py` — CaDiCaL on multiplier miter → LRAT → check; then
  the same statement via `bv_decide` in Lean; inspect `#print axioms`.

### B6. Why does a theorem prover call a SAT solver?
- **Objectives:** explain the motivation and the three integration styles; know
  exactly what is trusted in each.
- **Content:**
  - **Motivation:** finite/bit-vector goals are tedious by hand and decidable by
    machine; SAT turns them into one-liners (e.g. every per-opcode ALU fact).
  - **The LCF principle** (Milner): only a small kernel can create theorems;
    automation must *produce something the kernel checks*. So "just call the
    solver" is not allowed by default.
  - **Integration styles:**
    1. **Trusted oracle** — accept the solver's UNSAT; theorem tagged as
       oracle-dependent. (PVS's decision-procedure/Yices integration†; ACL2
       SATLINK via a trusted clause processor, Davis & Swords 2013.)
    2. **Proof replay/reconstruction** — translate the solver's proof into
       kernel inferences. (Isabelle `sat` tactic, Weber 2005–06†; HOL4 HolSat,
       Weber & Amjad 2009; Isabelle `smt` with Z3 proof reconstruction, Böhme &
       Weber 2010; Sledgehammer + `metis`/`smt`, 2007–.)
    3. **Certificate checking by reflection** — a checker *proven correct inside
       the prover* is executed on the solver's certificate. (SMTCoq for Coq,
       2011; Rocq `itauto`, Besson 2021; ACL2 verified LRAT checker, 2017;
       **Lean 4 `bv_decide`**: bit-blast in Lean, CaDiCaL produces LRAT, a
       verified Lean LRAT checker runs via compiled code — hence the
       `Lean.ofReduceBool` axiom.)
  - Trade-off table: speed vs. trusted base vs. proof size.
- **Lab:** prove an ALU fact three ways in Lean: `decide` (kernel evaluation,
  tiny widths only), `bv_decide` (SAT + LRAT), manual `BitVec` lemmas. Compare
  time and `#print axioms`.

### B7. History — has it always been this way?
- **Objectives:** place today's tools in context; answer "did Coq or older
  provers always use SAT?" — **No.**
- **Timeline (†verify exact years when writing):**

| Era | Theorem proving | SAT / model checking |
|---|---|---|
| 1960s | — | DP (1960), DPLL (1962) |
| 1970s | Stanford/Edinburgh **LCF** (Milner, 1972–79): kernel + tactics; Boyer–Moore prover (Nqthm) | Resolution theorem proving |
| 1980s | **HOL** (Gordon, mid-1980s) — *created for hardware verification*; **Coq** (Coquand & Huet, CoC 1984; Coq 1989); **Isabelle** (Paulson, 1986) | Temporal-logic MC (Clarke/Emerson; Queille/Sifakis, 1981) |
| 1990s | **PVS** (SRI, 1992) with built-in decision procedures; **ACL2** (Kaufmann & Moore); **AMD K5 FDIV proof in ACL2** after Pentium FDIV bug (1994–96) | BDD symbolic MC (SMV, 1992); GRASP (1996); BMC (1999) |
| 2000s | Intel **Forte** (STE + theorem proving, reFLect); Isabelle `sat` / HOL4 HolSat (proof replay); Sledgehammer (2007) | Chaff (2001), MiniSat (2003), interpolation (2003), Glucose (2009) |
| 2010s | SMTCoq (2011); Isabelle `smt` replay; ACL2 GL + SATLINK at Centaur; verified LRAT checkers (2017) | IC3/PDR (2011), Lingeling, CaDiCaL, DRAT/LRAT |
| 2020s | Lean 4; **`bv_decide`** (2024); Coq renamed **Rocq** (2025); CHERIoT-Ibex/Ibex proofs vs. Sail | Kissat; rIC3; open Ibex proof flow on Yosys + rIC3 |

  - Before ~2000 there was **no fast SAT to call**: provers relied on rewriting,
    induction, decision procedures (Presburger/omega, Nelson–Oppen, Shostak),
    and BDDs (Forte/STE, ACL2 hardware work).
  - Coq/Rocq's built-in automation (`tauto`, `lia`/`micromega`, `ring`) uses
    *decision procedures checked by reflection*, not SAT; SAT/SMT came via
    plugins (SMTCoq, itauto).
  - Hardware has been the driver throughout: HOL's origin, AMD/Intel/Centaur
    industrial proofs, and now Ibex.
- **Reading:** Gordon, *From LCF to HOL: a short history*; Harrison,
  *Handbook of Practical Logic and Automated Reasoning* (history chapters);
  Marques-Silva et al., *Handbook of Satisfiability* ch. "History"†.

---

## Part C — Lean foundations

### C1. Lean 4 for hardware engineers
- Types, functions, `structure`, pattern matching; `BitVec n`, `Fin n`, `Bool`
  vs `Prop`; `#eval` as simulation; `decide`. Lab: model a mux, adder, and
  counter by hand; simulate with `#eval`.

### C2. Propositions as types; the kernel
- What a proof term is; tactics build terms; `theorem` vs `def`; the kernel as
  the trusted base; axioms (`propext`, `Classical.choice`, `Quot.sound`,
  `Lean.ofReduceBool`); `#print axioms`. Lab: prove `x + 0 = x` four ways;
  inspect the term.

### C3. Tactics toolkit
- `intro`, `cases`, `induction`, `simp`, `omega`, `decide`, `bv_decide`,
  `grind`, `calc`; reading the infoview. Lab: tactic kata on BitVec facts.

---

## Part D — Twin labs

| Ch. | Topic | Design | Lean focus | MC focus | Key insight |
|---|---|---|---|---|---|
| D1 | Modelling RTL | counter, mux | `Circuit`, `run`, sv2lean output | — | RTL = state machine function |
| D2 | Safety | counter | `Safe`, unrolling, `BoundedSafe` | BMC | bounded ≠ proven; different theorems |
| D3 | Inductive invariants | one-hot FSM, wrap counter | `induction_sound`, strengthening | k-ind CEX, PDR | induction CEX = failing step goal; IC3 invariant pasted into Lean |
| D4 | SAT inside the prover | ALU slice | `bv_decide`, axioms | smtbmc+Bitwuzla | when to delegate leaf goals to SAT |
| D5 | Parameterized | ripple adder, FIFO(DEPTH) | `∀ n`, link lemmas | sweep WIDTH/DEPTH | the one thing Jasper can't do |
| D6 | Datapath | array multiplier | induction over bits, algebraic lemmas | SAT time vs width (chart) | SAT blow-up vs width-independent proof |
| D7 | Equivalence & refinement | adder variants; 3-stage teaching pipeline | simulation relation, Burch–Dill flushing | SEC-style miter | refinement generalises SEC |
| D8 | Liveness & fairness | round-robin arbiter(N) | ranking functions | liveness-to-safety, fairness assumptions | ∀N starvation-freedom |
| D9 | Protocols & assume-guarantee | valid/ready handshake, AXI-Lite-ish slave | lemma composition | assume-guarantee, helper assertions | helper assertions are lemmas |
| D10 | Crossing the gap | — | — | — | *Case study:* how lowRISC's Ibex proof uses theorem-proving-style lemma decomposition to make model checking converge (Ploix, DVClub 2025) |

---

## Part E — Capstone: lowRISC Ibex (OpenTitan's CPU)

See [CAPSTONE_IBEX.md](CAPSTONE_IBEX.md). Background reading for E0 is
[CAPSTONE_PRIMER.md](CAPSTONE_PRIMER.md).

### E0. Understanding the verification target (prerequisite block)
Goal: before proving anything about Ibex, be able to say precisely **what the
DUT is, what the spec is, and what the glue between them claims.**

- **E0.1 RISC-V for verifiers.** Architectural state, formats and scrambled
  immediates, extensions I/M/C/Zicsr, traps and privilege.
  *Lab:* decode 20 instruction words by hand, then check with
  `bv_decide` against the Lean spec's decoder. *Jasper mapping:* the ISA is
  the "spec document" behind every assertion you would write.
- **E0.2 Sail, the spec language.** Types with dependent widths, scattered
  `ast`/`encdec`/`execute`, `step`, backends (C++, SV, Lean), configuration of
  implementation-defined behaviour.
  *Lab:* build the sail-riscv emulator; run a small ELF; read the Sail for
  ADDI, BEQ, LW, C.ADDI, ECALL and write the Lean counterpart for the first three.
  *Jasper mapping:* Sail→SV is a machine-generated C2RTL-style reference model.
- **E0.3 Ibex microarchitecture tour.** IF (prefetch buffer, compressed
  decoder), ID/EX (decoder, controller FSM, ALU, multdiv, LSU, CSRs),
  register file, configs; **where architectural state lives** (abstraction map).
  *Lab:* run `examples/simple_system` in Verilator; read the `ibex_tracer` log;
  find, in the waveform, the cycle each instruction retires and the signals
  holding PC/x-regs.
- **E0.4 Co-simulation.** Ibex trace vs Sail emulator trace on the same ELF —
  the simulation-world version of the formal claim. *Lab:* inject a decoder
  bug and watch the traces diverge; then show riscv-formal catching it.
- **E0.5 RVFI and riscv-formal.** RVFI fields; the decomposition
  (`insn_*` relative to reported operands + `reg`/`pc_*`/`causal` for
  consistency); bounded depth; RVFI logic in the trust base.
  *Lab:* run `insn_add` and `reg` checks on Ibex; break RVFI wiring and see
  which check fails.
- **E0.6 Anatomy of the Ibex ⇔ Sail proof.** Observational correctness (why
  memory-operation order is the right claim when memory is outside the core);
  Sail→SV harness; lemma ordering; 1-/2-induction; trusted base.
  *Lab:* answer the primer's §7.3 reading-guide questions from the actual flow.
- **E0.7 Coverage matrix.** Who proves what (primer §8) — the frame for E5's
  retrospective.

### E1–E5. The capstone tracks
- **E1. Meet Ibex:** configuration, pipeline, RVFI, the formal story so far
  (CHERIoT-Ibex in Jasper; vanilla Ibex on Yosys + yosys-slang + rIC3).
- **E2. Track 1 — model checking the whole core:** run riscv-formal and the
  lowRISC open Sail-equivalence flow; study its lemma structure; re-run on
  Jasper at work (Jasper-side notes provided).
- **E3. Track 2 — Lean on blocks:** Lean RV32I spec; prove `ibex_alu`,
  `ibex_compressed_decoder`, register file, (optional) iterative multiplier
  against the spec.
- **E4. Track 3 — Lean slice (stretch):** refinement of a constrained
  ALU-instruction slice of the Ibex pipeline.
- **E5. Retrospective:** a written comparison — what each method found, cost,
  trust base, what would be needed for a full Lean proof.

---

## Reading spine (open/free unless noted)
- *Theorem Proving in Lean 4*; *Functional Programming in Lean*;
  *The Hitchhiker's Guide to Logical Verification* (Lean 4 ed.); Lean reference
  manual (`bv_decide`, `omega`, `grind`); *Mathematics in Lean* (optional).
- SAT: *Handbook of Satisfiability* (2nd ed., cite chapters; not free);
  Knuth TAOCP 4B §7.2.2.2 (not free); solver system descriptions (MiniSat,
  Glucose, CaDiCaL/Kissat SAT Competition papers).
- MC: BMC, k-induction, interpolation, IC3/PDR papers; YosysHQ SBY docs.
- History: Gordon *From LCF to HOL*; MacKenzie *Mechanizing Proof* (book, not free).
- Ibex: Ibex docs; lowRISC Ibex proof article; CHERIoT-Ibex arXiv paper; Ploix DVClub slides.
- RISC-V & Sail: RISC-V Unprivileged/Privileged specs; Armstrong et al.,
  *ISA Semantics for ARMv8-A, RISC-V, and CHERI-MIPS* (POPL 2019); sail-riscv
  README and model sources; riscv-formal / RVFI documentation.
