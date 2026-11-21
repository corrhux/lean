# Proof vs. Search — Product Specification

Status: **Draft v1 — approved direction, pending implementation**
Companion documents: [ARCHITECTURE.md](ARCHITECTURE.md) · [COURSE.md](COURSE.md) ·
[CAPSTONE_IBEX.md](CAPSTONE_IBEX.md) · [REFERENCES.md](REFERENCES.md)

---

## 1. Vision

A self-hosted learning lab that teaches **interactive theorem proving in Lean 4**
to an engineer who is already an expert in **SAT/SMT-based formal property
verification of RTL** (Cadence Jasper level). Every concept is taught by
contrast: the same SystemVerilog design is verified **twice, side by side**,
once with open-source model-checking engines (the Jasper-like view) and once in
Lean 4 (the proof view), and the learner sees concretely what each approach can
and cannot do.

The capstone uses a real, production open-source RISC-V core — **lowRISC Ibex**,
the main CPU of OpenTitan — rather than a toy core written for the course.

## 2. Target user

| Attribute | Assumption |
|---|---|
| Formal background | Expert: SVA, assume/assert/cover, BMC, k-induction, PDR/IC3 engines, CEX debug, helper assertions, cutpoints/abstraction, SEC, Jasper apps |
| SAT internals | **Not** assumed — user uses engines as black boxes; the course must teach solver internals and solver differences |
| Theorem proving | None. No Lean, Coq/Rocq, Isabelle, HOL, ACL2 background |
| Programming | Comfortable with SystemVerilog, scripting (Python/Tcl); functional programming not assumed |

## 3. Goals and non-goals

### Goals
- G1. Teach Lean 4 to the point of writing and proving properties of RTL models.
- G2. Explain precisely **how theorem proving differs from SAT-based model checking**:
  soundness/trust base, boundedness, invariants, parameterization, abstraction,
  liveness, counterexamples, automation vs. guidance.
- G3. Teach **SAT solver internals and the differences between solvers** (DPLL →
  CDCL, solver lineage, SMT, incremental SAT, proof certificates).
- G4. Explain **why theorem provers call SAT solvers**, the integration styles
  (oracle / replay / certificate checking), and the **history** across LCF, HOL,
  Isabelle, Coq/Rocq, ACL2, PVS, Lean.
- G5. Pull in **real open-source projects** (Lean, Yosys, SymbiYosys, ABC, rIC3,
  SAT/SMT solvers, riscv-formal, Ibex, Sail) — not re-implementations.
- G6. Provide an **AI tutor** that explains goals, CEXs and engine results in
  Jasper vocabulary and verifies its own suggestions before showing them.
- G7. Run fully locally/offline (except the optional tutor, which calls the Claude API).

### Non-goals
- N1. Not a general-purpose SystemVerilog → Lean compiler. `sv2lean` supports a
  documented synthesizable subset (plus whatever Ibex needs at module level).
- N2. Not a full Lean proof of Ibex end-to-end ISA correctness (that is a
  research project; see CAPSTONE_IBEX.md §5). The capstone deliberately splits
  the work between model checking (whole core) and Lean (blocks + slice).
- N3. Does not run or ship Cadence Jasper. Jasper equivalents are documented so
  the learner can re-run exercises at work; open-source engines stand in locally.
- N4. Not a replacement for the upstream books; the course links and cites them.

## 4. Delivery phases (decision: option C)

| Phase | Form | Contents |
|---|---|---|
| **Phase 1** | Repo + devcontainer + CLI + mdBook course | Lean library, RTL examples, `sv2lean`, `ftwin` CLI, `satlab`, tutor CLI, course book |
| **Phase 2** | Local web app (`docker compose up`) | Twin-pane UI, Lean infoview, Surfer waveform, benchmark charts, course reader, tutor pane — all built on Phase 1 components |

## 5. Core user workflows

**W1 — Read & do a module.** Open course chapter → read → run
`ftwin run <design>` → see both panes' results → open the Lean exercise
(`sorry` placeholders) → prove → `ftwin check <module>` confirms completion.

**W2 — Twin lab.** For one RTL design: run engines (BMC, k-induction, PDR/IC3)
and the Lean proof; compare status, depth, time, trust base (`#print axioms`),
and CEX waveform vs. Lean unsolved goal.

**W3 — Scaling benchmark.** `ftwin bench <design> --param WIDTH=4..64` → CSV +
chart of engine runtime vs. parameter alongside the single parametric Lean proof.

**W4 — SAT lab.** Step through the teaching CDCL solver on a BMC instance
derived from course RTL; run the same CNF through several real solvers;
generate and check a DRAT/LRAT UNSAT proof; watch `bv_decide` do the same inside Lean.

**W5 — Ask the tutor.** From CLI (`ftwin tutor`) or the pane: the tutor sees the
current module, file, Lean goal and last engine result and answers via a hint
ladder; any tactic it proposes has been compiled first.

**W6 — Capstone.** Run the Ibex open formal flow (model checking) and the
riscv-formal checks; prove Ibex sub-blocks in Lean against a Lean RV32I spec;
optionally attempt the pipeline slice refinement.

## 6. Functional requirements

### 6.1 Lean library (`RtlProof`)
- FR-L1 Circuit semantics: `Circuit`, `run`, traces, `Safe`, `Live` (with fairness).
- FR-L2 Meta-theory, fully proven (no `sorry`): soundness of BMC-to-depth-k
  (as bounded safety), 1-induction, k-induction, invariant strengthening,
  liveness-to-safety via ranking functions.
- FR-L3 Tactic helpers: `unroll k`, `rtl_simp` simp set, glue for `bv_decide`.
- FR-L4 ProofWidgets visualizer rendering a trace / goal state as a waveform.
- FR-L5 Each example: exercise file (with `sorry`) + solution file; CI checks
  solutions are sorry-free and use only allow-listed axioms.

### 6.2 RTL examples (`rtl/`)
- FR-R1 Authored SystemVerilog for: counter/one-hot FSM, ripple-carry adder,
  array multiplier, sync FIFO, round-robin arbiter, valid/ready handshake,
  teaching 3-stage pipeline (for the refinement module).
- FR-R2 Every design has a `.sby` with ≥ 3 engine configs (BMC, k-induction via
  smtbmc, PDR/IC3 via abc pdr and/or rIC3) and a README listing the equivalent
  Jasper SVA/Tcl.
- FR-R3 Parameterized designs expose WIDTH/DEPTH/N for benchmark sweeps.

### 6.3 `sv2lean` translator
- FR-T1 Input: SystemVerilog via Yosys + **yosys-slang** frontend → RTLIL →
  JSON. (Same frontend lowRISC uses for Ibex.)
- FR-T2 Output: Lean `structure State`, `structure Input`, `def step`,
  `def init`, outputs, named property predicates from `$assert`/`$assume` cells,
  and a generated theorem skeleton per property.
- FR-T3 Supported cells: `$add $sub $mul $and $or $xor $not $neg $shl $shr $sshr
  $eq $ne $lt $le $gt $ge (signed/unsigned) $logic_* $reduce_* $mux $pmux $bmux
  $concat/$slice $dff $adff $sdff $dffe $mem_v2 (sync write, async/sync read)
  $assert $assume $cover`. Unsupported cells → hard error with location.
- FR-T4 Memories map to `Fin depth → BitVec w`.
- FR-T5 Differential testing: random stimulus, Yosys `sim` vs Lean `#eval`,
  cycle-accurate match required, ≥ 1000 cycles × 20 seeds per design in CI.
- FR-T6 Link lemmas: for parameterized designs, a generated statement
  `generated_N = parametric N` at each benchmarked instance.

### 6.4 `ftwin` CLI
- FR-F1 `ftwin run <design> [--engines ...]` → normalized JSON + terminal report.
- FR-F2 `ftwin bench <design> --param P=a..b[:step]` → CSV + PNG/SVG chart.
- FR-F3 `ftwin check <module>` → exercise completion (sorry-free, axioms OK).
- FR-F4 `ftwin cex <design>` → open/convert VCD; summarize CEX in text for the tutor.
- FR-F5 `ftwin tutor` → interactive tutor session.
- FR-F6 `ftwin ibex ...` → wrappers for the capstone flows (see CAPSTONE_IBEX.md).

### 6.5 `satlab`
- FR-S1 Teaching DPLL and CDCL in readable Python (~500 LoC), emitting a JSON
  event trace: decide / propagate / conflict / analyze (1UIP) / learn /
  backjump / restart / reduce-db.
- FR-S2 Pluggable heuristics in the teaching CDCL (VSIDS vs. fixed order,
  restart policies Luby/glucose-style, phase saving on/off) to *show* their effect.
- FR-S3 Real-solver zoo via PySAT (MiniSat, Glucose, CaDiCaL, Lingeling,
  MapleSAT family …) + Kissat binary + Z3 + Bitwuzla (+ cvc5 optional).
- FR-S4 Instance generators: Tseitin from AIG/netlist, BMC unrolling of course
  RTL (via Yosys → AIGER → CNF), adder/multiplier miters, pigeonhole, random 3-SAT.
- FR-S5 Proof certificates: produce DRAT/LRAT with CaDiCaL, check with drat-trim
  / lrat-check; compare with `bv_decide` inside Lean.
- FR-S6 Incremental SAT demo: assumptions API, showing why BMC/IC3 rely on it.

### 6.6 Tutor
- FR-A1 Context: module id, open file, Lean goal(s) (via LSP), last `ftwin`
  result, CEX summary, user question.
- FR-A2 Hint ladder: nudge → concept → tactic → full step → full solution (only on request).
- FR-A3 Tools available to the model: `check_lean`, `run_sby`, `course_lookup`,
  `cex_summary`. Any proposed Lean code must pass `check_lean` before display.
- FR-A4 Jasper-vocabulary explanations (uses the Rosetta table as grounding).
- FR-A5 API key only via environment variable; model id configurable; prompt
  caching for static course context; per-session token/cost display.

### 6.7 Web app (Phase 2)
- FR-W1 Twin pane: SV editor + engine results + Surfer waveform | Lean editor + infoview.
- FR-W2 Course reader with "open in lab" links.
- FR-W3 Benchmark chart viewer.
- FR-W4 Tutor pane bound to the current lab state.
- FR-W5 Single-user, localhost-only by default; jobs sandboxed with time/memory limits.

### 6.8 Course
- FR-C1 Parts A–E as in COURSE.md, each chapter with objectives, reading,
  lab, Jasper mapping, and a "what changed vs. model checking" debrief.
- FR-C2 Every Lean code block compiled in CI; every SV block linted/elaborated in CI.

## 7. Non-functional requirements
- NFR-1 Reproducible: pinned versions for every tool; devcontainer + Docker image.
- NFR-2 Build time: `lake build` (no Mathlib) < 10 min cold on 8 cores;
  full CI (excluding Ibex full proof) < 30 min.
- NFR-3 Ibex open formal flow is opt-in (`make ibex-proof`), documented as
  ~45 min on a capable machine per lowRISC's report.
- NFR-4 Licensing: our code Apache-2.0; third-party code pulled as pinned git
  submodules or packages, never copied into our tree; licence table in REFERENCES.md.
- NFR-5 Offline-capable except the tutor.
- NFR-6 Platform: Linux x86_64 primary; macOS (arm64) best effort via devcontainer.

## 8. Milestones & acceptance criteria

| # | Deliverable | Accepted when |
|---|---|---|
| M0 | Skeleton, pinned toolchains, devcontainer, CI, licence audit | `lake build`, `pytest`, `sby` smoke test, `mdbook build` all green in CI |
| M1 | Lean core + meta-theory; Counter & Adder twins; `ftwin run` | k-induction soundness theorem proven; both twins report on both sides |
| M2 | `sv2lean` + differential testing | All Part D designs translate; diff tests pass |
| M3 | `satlab` + Course Part B (SAT, certificates, history) | CDCL trace viewer works; solver zoo table reproducible; LRAT demo checks |
| M4 | Remaining examples, `ftwin bench`, Parts A, C, D | Multiplier scaling chart produced; all exercise solutions sorry-free |
| M5 | Ibex capstone (see CAPSTONE_IBEX.md) | Tracks 1 & 2 complete; Track 3 slice documented (proven or honestly scoped) |
| M6 | Tutor CLI | Tutor answers on 10 scripted scenarios; all suggested code compiles |
| M7 | Web app | All W1–W6 workflows usable in the browser |

## 9. Open items to confirm at M0
- Exact pinned versions (Lean toolchain, Yosys/yosys-slang, rIC3, Ibex commit).
- Whether Ibex's compressed (C) extension can be disabled by parameter, or must
  be handled by assumption / modelled in the Lean spec (CAPSTONE_IBEX.md §4).
- Maturity of the Sail → Lean backend for `sail-riscv` (optional spec cross-check).
- Licences of every pulled project (REFERENCES.md table marks unverified ones).
