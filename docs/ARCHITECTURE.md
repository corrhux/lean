# Proof vs. Search — Architecture

Status: **Draft v1** · Companion to [SPEC.md](SPEC.md)

---

## 1. System overview

```
                        ┌───────────────────────────────────────────────┐
                        │ course/  (mdBook)  reading + exercises + labs │
                        └──────────────────────┬────────────────────────┘
                                               │ "open in lab" links
  rtl/*.sv ─┐                                  │
  third_party/ibex ─┤                          │
            ▼                                  │
   Yosys + yosys-slang ──► RTLIL ──► JSON ──► tools/sv2lean ──► RtlProof/Generated/*.lean
            │                                                         │
            ├─► SymbiYosys (.sby) ─► smtbmc(+Bitwuzla/Z3/Yices)       │  lake build / LSP
            │                      ─► abc pdr / abc bmc3              │  goals, axioms, time
            ├─► AIGER ─► rIC3 (IC3/PDR, used by Ibex open proof)      │
            └─► AIGER ─► CNF ─► satlab (teaching CDCL + solver zoo)   │
                     │ status, depth, time, CEX .vcd                  │
                     ▼                                                ▼
              tools/ftwin  — orchestration, normalised Result JSON, benchmarks
                │
                ├─► terminal report / CSV / charts           (Phase 1)
                ├─► tutor/  (Claude API tool-use loop)       (Phase 1 CLI, Phase 2 pane)
                └─► app/backend (FastAPI)  ◄──►  app/frontend (React)   (Phase 2)
                         │                         Monaco · Lean infoview ·
                         └─ job sandbox            Surfer (WASM) · charts · tutor
```

Design principle: **one RTL source of truth feeds both panes.** Every
difference the learner sees is a difference of *method*, not of modelling.

## 2. Repository layout

```
lean/                                   (this repo)
├── README.md
├── docs/                               SPEC, ARCHITECTURE, COURSE, CAPSTONE_IBEX, REFERENCES
├── lean-toolchain                      pinned Lean 4 release
├── lakefile.lean, lake-manifest.json
├── RtlProof/                           Lean library
│   ├── Core/        Circuit.lean, Trace.lean, Safety.lean, Liveness.lean, BitVecExtra.lean
│   ├── Meta/        BMC.lean, Induction.lean, KInduction.lean, Ranking.lean
│   ├── Tactics/     Unroll.lean, RtlSimp.lean
│   ├── Widgets/     Waveform.lean              (ProofWidgets4)
│   ├── Fluency/     L01…L17 Exercise.lean / Solution.lean  (course Part C drills)
│   ├── Generated/   *.lean                     (sv2lean output; committed, CI-regenerated)
│   ├── Examples/    Counter/ Adder/ Multiplier/ Fifo/ Arbiter/ Handshake/ Pipe3/
│   │                  each: Model.lean  Exercise.lean  Solution.lean  Param.lean (if parametric)
│   └── RV32I/       Spec/ (Decode, Exec, State)  Ibex/ (Alu, CompressedDecoder,
│                      Decoder, RegFile, MultDiv, Slice)
├── rtl/<design>/    <design>.sv  <design>.sby  README.md (Jasper SVA/Tcl equivalents)
├── capstone/ibex/   configs, wrapper RTL (RVFI glue), .sby/.sh flows, Makefile
├── tools/
│   ├── sv2lean/     Python package: frontend.py ir.py lower.py emit_lean.py difftest.py
│   └── ftwin/       Python package: cli.py runners/{sby,lean,ric3,ibex}.py result.py bench.py
├── satlab/          dpll.py cdcl.py heuristics/ gen/ zoo.py certs.py viewer/
├── tutor/           context.py tools.py prompts/ ladder.py client.py
├── course/          book.toml  src/SUMMARY.md  src/<part>/<chapter>.md
├── app/             backend/ (FastAPI)  frontend/ (React + Vite)
├── third_party/     git submodules (pinned): ibex, riscv-formal, sail-riscv (optional)
├── .devcontainer/   devcontainer.json → docker/Dockerfile
├── docker/          Dockerfile, compose.yaml
└── .github/workflows/ci.yml
```

Third-party *source* lives only under `third_party/` as submodules. Third-party
*tools* are installed into the image, not committed.

## 3. Toolchain matrix (pin exact versions at M0)

| Layer | Component | Role | Install method |
|---|---|---|---|
| Prover | Lean 4 + Lake (via elan) | Proof side | `lean-toolchain` file |
| Prover | `Std.Tactic.BVDecide` (core) | Bit-blasting + CaDiCaL + verified LRAT check | built into Lean |
| Prover | ProofWidgets4 | Waveform widget in infoview | Lake dependency |
| Prover | Mathlib4 | **Not initially**; add only if `ring`-style algebra needed | Lake dependency (deferred) |
| HDL | Yosys | Elaboration, RTLIL, JSON/AIGER/BTOR2 export, `sim` | OSS CAD Suite |
| HDL | yosys-slang (plugin) | SystemVerilog frontend (needed for Ibex; used for all designs) | OSS CAD Suite / source build |
| HDL | sv2v | Fallback SV→Verilog for riscv-formal's Ibex flow | OSS CAD Suite |
| MC | SymbiYosys | Jasper-like task runner (BMC, prove, cover) | OSS CAD Suite |
| MC | ABC | `pdr`, `bmc3`, SAT sweeping | OSS CAD Suite |
| MC | rIC3 | IC3/PDR engine used by lowRISC's open Ibex proof | cargo / release |
| MC | Pono (optional) | Extra word-level engines (k-ind, IC3IA) | source build |
| SAT/SMT | CaDiCaL, Kissat | Reference CDCL solvers, DRAT/LRAT output | OSS CAD Suite / source |
| SAT/SMT | PySAT | Python access to MiniSat/Glucose/CaDiCaL/Lingeling/Maple* | pip |
| SAT/SMT | Z3, Bitwuzla, (cvc5) | SMT / word-level BV | pip / OSS CAD Suite |
| Certs | drat-trim, lrat-check | UNSAT proof checking | source build |
| Waves | Surfer | VCD viewer (desktop + WASM for web app) | release / npm-served WASM |
| Course | mdBook | Book build | cargo |
| RISC-V | lowRISC Ibex | Capstone DUT | submodule |
| RISC-V | riscv-formal | RVFI-based ISA checks | submodule |
| RISC-V | sail-riscv + Sail | Golden spec; **emulator for co-simulation labs (E0)**; optional Sail→Lean cross-check | submodule + opam (OCaml 5.x) / release binary |
| RISC-V | Verilator | Simulate Ibex `simple_system` for E0 labs | OSS CAD Suite / distro |
| RISC-V | RISC-V GCC (rv32 bare-metal) | Compile lab programs (ELF) | prebuilt toolchain release |
| Tutor | Anthropic Python SDK | Tutor model calls | pip |

**Network hosts needed on the implementation machine** (the cloud sandbox used
to write these docs blocks some of them): `github.com` +
`objects.githubusercontent.com` (elan, OSS CAD Suite, rIC3 releases, submodules),
`releases.lean-lang.org`, Lake/Mathlib cache hosts (only if Mathlib is added),
`pypi.org`, `registry.npmjs.org`, `crates.io`, `opam.ocaml.org` (Sail only),
`api.anthropic.com` (tutor only).

## 4. Component design

### 4.1 Lean semantic core (`RtlProof/Core`)

```lean
structure Circuit (I S : Type) where
  init : S
  step : S → I → S

def run (c : Circuit I S) (ins : Nat → I) : Nat → S
  | 0     => c.init
  | n + 1 => c.step (run c ins n) (ins n)

/-- SVA `assert property (P)` with no assumptions. -/
def Safe (c : Circuit I S) (P : S → Prop) : Prop :=
  ∀ ins n, P (run c ins n)

/-- With environment assumptions (SVA `assume`): only input streams satisfying A. -/
def SafeUnder (c : Circuit I S) (A : S → I → Prop) (P : S → Prop) : Prop :=
  ∀ ins, (∀ n, A (run c ins n) (ins n)) → ∀ n, P (run c ins n)

def BoundedSafe (c : Circuit I S) (P : S → Prop) (k : Nat) : Prop :=
  ∀ ins n, n ≤ k → P (run c ins n)          -- what a BMC "bounded proof to k" means
```

`RtlProof/Meta` (all fully proven) — the engines' algorithms as theorems:

```lean
theorem induction_sound (Inv : S → Prop)
    (h0 : Inv c.init) (hstep : ∀ s i, Inv s → Inv (c.step s i))
    (hP : ∀ s, Inv s → P s) : Safe c P

theorem kinduction_sound (k : Nat)
    (hbase : BoundedSafe c P k)
    (hstep : ∀ s ins, (∀ j ≤ k, P (runFrom c s ins j)) → P (runFrom c s ins (k+1))) :
    Safe c P

theorem ranking_live (rank : S → Nat) ... : Live c Q   -- liveness via well-founded measure
```

These make the Jasper vocabulary precise: an *induction CEX* is a concrete
`s` violating `hstep` that is not reachable — the learner sees exactly which
hypothesis fails.

### 4.2 `sv2lean` translator

Pipeline:

```
.sv ──yosys -m slang: read_slang; hierarchy -top T; proc; flatten; opt_clean;
      memory_collect; (async2sync | clk2fflogic as configured); write_json
   ──► ir.py      typed IR: Wire{name,width,signed}, Cell{type,params,ports},
                  Reg{d,q,clk,rst,en,init}, Mem{width,depth,rd/wr ports}, Prop{kind,expr,label}
   ──► lower.py   topological sort of comb cells; reject comb loops; single clock domain
                  check; reset → init; enables → mux
   ──► emit_lean.py
```

Emitted Lean (shape):

```lean
namespace Gen.Counter
structure State where  cnt : BitVec 4   deriving Repr, DecidableEq
structure Input where  en  : Bool       deriving Repr
def init : State := ⟨0#4⟩
def step (s : State) (i : Input) : State := ⟨if i.en then s.cnt + 1#4 else s.cnt⟩
def circuit : Circuit Input State := ⟨init, step⟩
-- from `assert (cnt != 4'd12)` labelled p_never_12
def p_never_12 (s : State) : Prop := s.cnt ≠ 12#4
theorem p_never_12_holds : Safe circuit p_never_12 := by sorry  -- exercise
end Gen.Counter
```

Decisions:
- **Frontend = yosys-slang** for every design (it is what lowRISC uses for Ibex,
  so one frontend covers course designs and capstone). sv2v kept only for
  riscv-formal's own Ibex flow.
- **Single clock, synchronous semantics.** Async resets converted with
  `async2sync`; multi-clock designs out of scope.
- **Names preserved** (`\` and `.` mangled deterministically) so Lean goals read
  like the RTL.
- **Large designs** (Ibex blocks): emit one `def` per combinational cone with
  `@[irreducible]` boundaries at module ports to keep elaboration and `simp`
  tractable; `bv_decide` is applied per cone.
- **Trust:** differential testing (`difftest.py`): random inputs →
  `yosys sim -vcd` vs. Lean `#eval` trace → compare every register every cycle.

### 4.3 `ftwin` orchestrator

Normalised result (one per side per run):

```json
{
  "design": "fifo", "params": {"DEPTH": 8, "WIDTH": 16},
  "side": "mc",                       // "mc" | "lean"
  "engine": "abc pdr",                // or "smtbmc bitwuzla", "rIC3", "lean"
  "property": "p_no_overflow",
  "status": "proven",                 // proven | cex | bounded | unknown | error
                                      // lean: proved | sorry | error
  "depth": 12,                        // bmc depth / k / IC3 frame count
  "time_s": 3.41,
  "cex_vcd": "out/fifo/p_no_overflow.vcd",
  "lean": {"goals": [], "axioms": ["propext", "Classical.choice", "Quot.sound",
                                   "Lean.ofReduceBool"]},
  "log": "out/fifo/abc_pdr.log"
}
```

`axioms` is surfaced deliberately: `Lean.ofReduceBool` appears exactly when a
proof relied on `bv_decide`/`native_decide`, which is the course's concrete
handle on "what you are trusting".

Runners: `sby.py` (generates per-engine `.sby` from a template + design
config), `lean.py` (`lake env lean --json` + `#print axioms` probe), `ric3.py`
(AIGER in, witness out → VCD via `yosys-witness`), `ibex.py` (capstone wrappers:
`rvfi`, `sail-proof`, `cosim`).

`ftwin ibex cosim <elf>`: build Ibex `simple_system` (Verilator) → run ELF →
parse `ibex_tracer` log; run the Sail emulator on the same ELF with
instruction tracing → normalise both to `(order, pc, insn, rd, rd_wdata,
mem_addr, mem_wdata)` → first-divergence report. Used by course E0.4.

`bench.py`: parameter sweep → re-elaborate → run engines with timeout →
CSV (`design,param,engine,status,time_s`) → chart (matplotlib, SVG).

### 4.4 `satlab`

- `dpll.py`, `cdcl.py`: clarity over speed. CDCL implements 2-watched-literals,
  1UIP conflict analysis, clause minimisation (optional), EVSIDS, Luby and
  glucose-style restarts, phase saving, LBD-based reduction. Every step emits an
  event to `trace.jsonl`.
- `viewer/`: terminal stepper in Phase 1; implication-graph + trail view in Phase 2.
- `gen/`: Tseitin (from Yosys AIGER via `aigtocnf`-equivalent Python), BMC
  unrolling k-frames, miters, pigeonhole, random k-SAT.
- `zoo.py`: same CNF → N solvers → table of time / conflicts / decisions / props.
- `certs.py`: CaDiCaL `--lrat`/DRAT → drat-trim / lrat-check; plus a Lean file
  that runs `bv_decide` on the equivalent BitVec statement for comparison.
- `incremental.py`: assumption-based incremental BMC and a mini IC3 loop
  (`frame`, `block`, `propagate`) using PySAT incremental API — the mechanism
  behind Jasper's PDR-class engines.

### 4.5 Tutor

```
UI (CLI / pane) ─► context.py: {module, file excerpt, goals (LSP $/lean/plainGoal),
                                last Result JSON, CEX summary, question, ladder level}
               ─► client.py: Messages API, tool-use loop, prompt caching on
                             static blocks (Rosetta table, chapter text)
               ◄─ tools.py:  check_lean(code) → {ok, errors, goals}
                             run_sby(design, engine) → Result JSON
                             course_lookup(chapter_id) → text
                             cex_summary(vcd) → per-cycle table of key signals
```

- System prompt rules: explain in Jasper terms; obey ladder level; never show
  Lean that has not passed `check_lean`; cite course chapters.
- Config: `ANTHROPIC_API_KEY` env var; `TUTOR_MODEL` env var (default: latest
  Claude model at implementation time); max tool iterations; spend display.
- Implementation detail to settle at M6: consult current Anthropic SDK docs for
  the tool runner / caching APIs.

### 4.6 Web app (Phase 2)

- **Backend (FastAPI):** `POST /run`, `POST /bench`, `GET /result/{id}`,
  `WS /lean` (proxy to a Lean server per user workspace), `POST /tutor` (SSE
  stream), `GET /vcd/{id}`. Jobs run in a subprocess sandbox (rlimits, timeouts,
  per-job temp dir). Localhost-only by default.
- **Frontend (React + Vite):** Monaco (SV + Lean), `@leanprover/infoview` (the
  component used by lean4web / VS Code), Surfer WASM in an iframe for VCDs,
  chart component, mdBook HTML embedded for the reader, tutor pane.

## 5. CI design

| Job | Steps |
|---|---|
| lean | `lake build`; compile all `Solution.lean`; assert no `sorry`; axiom allow-list check |
| course | extract ```lean blocks → `lake env lean`; extract ```systemverilog → `yosys read_slang`; `mdbook build` |
| rtl | `sby` on every design (fast engines, small params) |
| sv2lean | unit tests + regenerate `Generated/` and `git diff --exit-code` + difftest |
| satlab | pytest; zoo smoke on tiny CNFs; LRAT check demo |
| ibex-blocks | sv2lean on Ibex sub-blocks + Lean block proofs (Track 2) |
| ibex-full (nightly/manual) | lowRISC open proof flow + riscv-formal checks (Track 1) |

## 6. Architecture decisions (ADR summary)

| # | Decision | Rationale |
|---|---|---|
| ADR-1 | Phase 1 CLI + book, Phase 2 web app | Learning value is in content and twin labs; web reuses everything |
| ADR-2 | Learner-authored SV for Parts A–D; **Ibex for capstone** | Small designs teach technique; Ibex gives real-world scale and an existing industrial proof to study |
| ADR-3 | yosys-slang as the single SV frontend | Handles Ibex's SV; matches lowRISC's open flow |
| ADR-4 | Fixed-width generated models + hand-written parametric models + link lemmas | Yosys elaborates one parameter set; ∀-width claims need a parametric model |
| ADR-5 | No Mathlib initially | Core Lean has BitVec, `bv_decide`, `omega`, `simp`, `grind`; keeps builds small |
| ADR-6 | Translator trusted via differential testing, not proven | Proving sv2lean correct is out of scope; differential testing is explicit and measurable |
| ADR-7 | Hand-written Lean RV32I spec; Sail-generated Lean as optional cross-check | Readable teaching spec; Sail Lean backend maturity to be confirmed |
| ADR-8 | Keep a 150-line teaching pipeline in Part D | Learning Burch–Dill refinement on Ibex directly is too steep |
| ADR-9 | Tutor must compile suggestions before showing them | Prevents confident-but-wrong tactic advice |
