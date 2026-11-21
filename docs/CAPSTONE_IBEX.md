# Capstone: lowRISC Ibex (OpenTitan's RV32 core)

Status: **Feasibility analysis + plan** · Replaces the "write our own RV32I core" capstone.

---

## 1. Question and answer

> *Can the RV32I capstone use an OpenTitan core from open source instead of
> writing one ourselves?*

**Yes.** OpenTitan's main CPU is **lowRISC Ibex** (Apache-2.0,
`github.com/lowRISC/ibex`, also vendored into OpenTitan under
`hw/vendor/lowrisc_ibex`). It is a better capstone than a self-written core
because:

1. **It already has an industrial-grade formal proof against the official ISA
   spec — done both ways you care about:**
   - *Commercial:* CHERIoT-Ibex was proven against its Sail ISA spec using
     **Cadence Jasper**, with Sail compiled to SystemVerilog as the reference
     model (Oxford / lowRISC / Microsoft; arXiv 2502.04738).
   - *Open source:* lowRISC re-did the proof for vanilla Ibex on an **open
     toolchain — yosys-slang (SV frontend with an SVA-subset extension) →
     Yosys → AIGER → rIC3** — run in Ibex CI, all properties converging in
     under ~45 minutes on a capable machine. The proven statement: Ibex and the
     Sail RISC-V spec perform the same memory operations in the same order for
     equivalent inputs.
   - The approach is explicitly about **"crossing the model-checking /
     theorem-proving gap"** (Ploix, DVClub Cambridge 2025): most properties
     close by 1- or 2-induction because end-to-end results are reused as
     lemmas. That is *exactly* this course's theme, on a real core.
2. **It has an RVFI port and an existing riscv-formal flow** (Ibex's `formal/`
   directory builds a single Verilog file with sv2v + Yosys for riscv-formal;
   historically with the M extension disabled).
3. You can **re-run the same flow on Jasper at work** and compare engines.

**What is *not* realistic:** a complete Lean proof that the whole Ibex core
refines the RV32 ISA. Ibex has CSRs, exceptions, interrupts, debug mode, PMP,
compressed instructions, multi-cycle mult/div, a prefetch buffer, and security
hardening. Generated from flattened RTL, the Lean state would have thousands of
bits of state and the proof would be a research project measured in
person-months. The capstone therefore **splits the work** the way industry
does — and that split is itself a lesson.

## 2. Ibex facts relevant to the plan (verify at M0 against the pinned commit)

| Item | Note |
|---|---|
| ISA | RV32IMC(B) — base config "small" is RV32IMC, 2-stage pipeline (IF, ID/EX), optional writeback stage |
| Configs | `ibex_configs.yaml` (`small`, `opentitan`, `maxperf`, …) via `util/ibex_config.py` |
| Parameters | `RV32E`, `RV32M` (None/Slow/Fast/SingleCycle), `RV32B` (None/…/OTEarlGrey), `PMPEnable`, `ICache`, `WritebackStage`, `BranchTargetALU`, `SecureIbex`, … |
| Compressed (C) | Appears always enabled (no parameter found) — **verify**. If not disable-able: constrain via assumption *or* include C in the Lean spec (preferred; see Track 2). |
| Frontends | Plain Yosys cannot parse Ibex SV; use **yosys-slang** (lowRISC's open proof) or **sv2v** (riscv-formal/syn flows) |
| Formal assets | `formal/` (riscv-formal glue); lowRISC's Sail-equivalence proof flow (locate exact path at pinned commit) |

## 3. Capstone configuration ("capstone" config)

Start from `small` and minimise for proof:

```
RV32E=0  RV32M=RV32MNone (Track 2 optional: RV32MSlow)  RV32B=RV32BNone
PMPEnable=0  ICache=0  WritebackStage=0  BranchTargetALU=0
SecureIbex=0  DbgTriggerEn=0
```

Environment assumptions for Track 3 only: no interrupts, debug request held
low, instruction/data memory always grants with no errors (idealised memory),
optionally 32-bit (non-compressed) encodings only.

## 4. Three tracks

### Track 1 — Model checking the whole core (reproduce industry)
- **1a. riscv-formal on Ibex via RVFI.** `ftwin ibex rvfi` → build
  `formal/ibex.v` (sv2v + Yosys) → riscv-formal checks (`insn_*`, `reg`,
  `pc_fwd/bwd`, `causal`, `liveness`) at bounded depth with SBY.
  *Teaches:* per-instruction bounded checks; bounded vs. unbounded.
- **1b. lowRISC open Sail-equivalence proof.** `ftwin ibex sail-proof` →
  run Ibex's own flow (yosys-slang + Yosys + rIC3). Study:
  - Sail → SystemVerilog reference model (one combinational "event" per instruction/fetch-error/interrupt)
  - property/lemma decomposition, the proof conductor, 1-/2-induction closure.
  *Teaches:* how lemma structure (a theorem-proving idea) makes model checking converge.
- **1c. Jasper notes.** A guide for re-running 1a/1b on Jasper (engine
  choices, proof grid, helper-assertion structure) — the learner does this at work.

### Track 2 — Lean on Ibex blocks (achievable, the core Lean work)
Lean RV32I(+C) spec in `RtlProof/RV32I/Spec` (hand-written, ~600 LoC:
`decode`, `exec`, `ArchState`, C-expansion function). Then, using sv2lean on
individual Ibex modules (yosys-slang, module-level elaboration):

| Block | Property | Expected method |
|---|---|---|
| `ibex_alu` | For every ALU operator used by RV32I: result = spec semantics | `bv_decide` per op; case split on operator enum |
| `ibex_compressed_decoder` | Every valid C instruction expands to the 32-bit instruction the spec's C-expansion gives; illegal ones flagged | `bv_decide` (finite, 16-bit input) — also a nice SAT-vs-Lean comparison |
| `ibex_register_file_ff` | x0 reads 0; read-after-write; no spurious writes | induction over cycles + `simp` |
| `ibex_decoder` (subset) | Decoded control signals match spec `decode` for RV32I opcodes | `bv_decide` / case analysis |
| `ibex_multdiv_slow` (optional, needs RV32M) | Iterative multiplier/divider computes spec result after N cycles | **sequential invariant proof** — the place SAT struggles at 32 bits and Lean induction shines (ties to D6) |

### Track 3 — Lean pipeline slice (stretch)
- Scope: Ibex with the capstone config + Track 3 assumptions, executing only
  RV32I register–register and register–immediate ALU instructions (no loads,
  stores, branches, CSRs).
- Statement: refinement — every instruction retired (RVFI `valid`) updates the
  architectural state exactly as `Spec.exec` does (commuting diagram), using an
  abstraction function from Ibex state to `ArchState`.
- Method: Burch–Dill-style flushing abstraction (practised on the teaching
  pipeline in D7), block lemmas from Track 2 as building blocks, `bv_decide`
  on leaf obligations.
- **Acceptance:** either the slice is proven, or a written report documents
  the stuck points (state-space size, elaboration time, abstraction needed).
  Both outcomes meet the learning objective.

### Optional — Sail-generated Lean spec cross-check
The Sail compiler has a Lean backend that can generate a Lean model from
`sail-riscv` (reports indicate it needs OCaml 5.x; maturity to be confirmed).
If usable: prove or differential-test that the hand-written spec agrees with
the Sail-generated Lean on the RV32I subset — closing the loop to the same spec
lowRISC proves Ibex against.

## 5. Why not a full Lean proof of Ibex? (content for E5)
- State size: Ibex has hundreds of flops plus CSR/PMP state; flattened Lean
  model is huge; `simp`/elaboration costs grow badly without abstraction.
- Feature surface: exceptions, interrupts, debug, misaligned access splitting,
  prefetch buffer, multi-cycle units.
- Precedent: full-core ITP proofs (e.g. Kami-based cores in Coq, CakeML's
  Silver CPU in HOL4) were designed *with* the prover; retrofitting an existing
  industrial core is a different, harder problem — which is why lowRISC chose
  model checking with heavy lemma structure.
- The honest lesson: **model checking for whole-core breadth; theorem proving
  for parameterised blocks, deep datapath, and the meta-level (soundness of
  the method itself).**

## 6. Deliverables & effort estimate

| Item | Est. effort |
|---|---|
| Submodules, capstone config, build glue, `ftwin ibex` wrappers | 3–5 days |
| Track 1a + 1b running in CI (nightly) + course E1/E2 | 1 week |
| Lean RV32I(+C) spec | 1 week |
| Track 2 blocks (ALU, compressed decoder, regfile, decoder subset) | 2–3 weeks |
| Track 2 multdiv (optional) | 1–2 weeks |
| Track 3 slice | 3–6 weeks, research-risk |
| Course E3–E5 | 1 week |

## 7. Risks
| Risk | Mitigation |
|---|---|
| sv2lean can't handle some Ibex module constructs | Module-level translation only; add cells incrementally; fall back to hand-modelled Lean + difftest |
| Ibex formal flow paths/tools change upstream | Pin Ibex commit; document versions |
| rIC3 / yosys-slang versions incompatible with OSS CAD Suite build | Build both from source in the Docker image |
| Track 3 intractable | Scoped as stretch with "report" acceptance |
