# Proof vs. Search

A learning lab for **Lean 4 theorem proving**, aimed at engineers who already
know **SAT-based RTL formal verification** (Jasper-class model checking). The
same SystemVerilog design is verified twice, side by side: once with
open-source model-checking engines and once in Lean, so the differences in
method are visible.

The course also covers SAT/SMT solver internals and how the solvers differ, why
theorem provers call SAT solvers, and the history behind both (LCF, HOL, Coq/Rocq,
Isabelle, ACL2, Lean). The capstone uses **lowRISC Ibex**, the RISC-V core in
OpenTitan.

## Status

| Milestone | State |
|---|---|
| M0 skeleton | Lake project (`lakefile.toml`, Lean 4.36.0), Python package, CI, Docker image and dev container are in place. `lake build` passes. |
| M1 Lean core | Circuit semantics, model-checker assumption semantics (`SafePrefix`), and **proven** soundness of induction, k-induction and invariant-with-assumptions (`RtlProof/Meta`). Counter twin proven in Lean on the generated model. |
| M1b Lean fluency | All 48 code blocks in [docs/LEAN_FLUENCY.md](docs/LEAN_FLUENCY.md) compile on Lean 4.36.0, and the 3 intentional failures fail (`tools/lean_blocks.py`, run in CI). |
| M2 sv2lean | **Working**: SystemVerilog → Yosys → Lean (`tools/sv2lean`). Differential-tested against Yosys's own semantics; mutation tests show the difftest catches injected bugs. |
| `ftwin` | `ftwin run <design>`: SymbiYosys tasks and Lean theorems side by side (`tools/ftwin`). |
| Twin labs | `rtl/counter`, `rtl/mul`, `rtl/fifo`, `rtl/arbiter`: each proven on both sides. Lean proves the **multiplier algorithm for every width**, the **FIFO control for every depth** and **round-robin fairness for every N**, then links each to the generated RTL. Measured scaling is in each design's README. `ftwin bench <design>` sweeps the parameter. |
| M3 satlab | **Working and tested**: teaching DPLL/CDCL with traces, generators, solver zoo (including CaDiCaL and Kissat), DRUP proof checking. See [satlab/README.md](satlab/README.md). |
| M5 Ibex capstone | **Track 2 done for the decode/execute blocks; the rest is an exam.** lowRISC Ibex pinned as a submodule and translated unmodified (via sv2v). Proven against a Lean RV32I/RV32C spec written from the ISA manual: the ALU, the decoder (every RV32I instruction class plus Zicsr, Zifencei, MRET, WFI, DRET), the compressed decoder (all 49,152 encodings) and the register file; decoder + ALU composed into instruction-level theorems. The **load/store unit and the multiplier/divider are the Ibex exam** ([capstone/exam](capstone/exam/README.md)): 8 graded statements (100 points) plus an open challenge, prepared by chapters E5–E11 ([docs/CAPSTONE_EXAM_PREP.md](docs/CAPSTONE_EXAM_PREP.md)), graded by `pvs-exam`, with reference solutions CI checks. **Not done:** Track 1 (Ibex vs. Sail needs Jasper or the native CAD suite: a practical for your machine) and Track 3 (pipeline refinement, outlined in E11). See [capstone/ibex/README.md](capstone/ibex/README.md). |
| M6 tutor | `tutor ask/chat` (`tools/tutor`): Claude explains in Jasper terms on a 5-level hint ladder, with tools to compile Lean, look up course sections, read files, summarise counterexample waveforms and run twins. Tools are tested offline; the live API path needs `ANTHROPIC_API_KEY`. |
| M7 web app | `pvs-app` (`app/`): a local, offline browser front end over the same tools. **Course reader**; **twin labs** where you edit the RTL and the Lean solution, run both sides on your version (the Lean model is regenerated from your RTL), read counterexamples and induction traces in a **waveform viewer**, and chart **parameter sweeps** (one MC run per value against one Lean theorem); a **live Lean editor** with errors as you type and the goal at the cursor (Lean's language server, as in VS Code); an **Ibex exam** view (edit, live goals, grade); the SAT solver zoo; and a **streaming tutor** that sees what you are working on. The tutor's live API path is untested here (no key). |

## Quick start (macOS or Linux)

```sh
git clone https://github.com/corrhux/lean.git && cd lean
./start
```

That is all. `./start` checks for Python 3.11+ (on a Mac: `brew install python@3.12`
if it says so), offers to install Lean, installs the course tools into `.venv`,
builds the Lean library, and opens the course app at http://127.0.0.1:8000. The
first run takes 10–20 minutes (downloading Lean and checking every proof); later
runs take seconds. Everything runs on your machine; nothing listens beyond
`127.0.0.1`. The optional AI tutor needs `ANTHROPIC_API_KEY=... ./start`.

The app is the whole course in one window:

| View | What you do there |
|---|---|
| **Course** | read the chapters, in order, starting with the course index |
| **Twin labs** | run SymbiYosys and Lean on the same design; edit the RTL or the proof and rerun; counterexample waveforms; parameter sweeps |
| **Lean workbook** | the lab exercises and a scratchpad, checked as you type, with the goal at the cursor |
| **Ibex exam** | the capstone exam, with grading |
| **SAT lab** | satlab's five labs at a click, and the solver zoo |
| **Tutor** | questions about whatever you are working on (optional, needs an API key) |

Every view is also a command (`ftwin`, `satlab`, `sv2lean`, `pvs-exam`, `tutor`), for
those who prefer a terminal; the course index gives both.

## The course

Start at **[course/README.md](course/README.md)**: every chapter with what to read, what to run and which files hold the exercise and solution.

## Documents

| Document | Contents |
|---|---|
| [docs/SPEC.md](docs/SPEC.md) | Goals, workflows, requirements, milestones |
| [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md) | Components, repo layout, toolchain, interfaces, CI, design decisions |
| [docs/COURSE.md](docs/COURSE.md) | Full syllabus, Parts A–E, including the SAT and history chapters |
| [docs/LEAN_FLUENCY.md](docs/LEAN_FLUENCY.md) | Course Part C: the Lean language and its semantics in plain terms, in 18 lessons with RTL/Jasper analogies, drills and solutions |
| [docs/CAPSTONE_PRIMER.md](docs/CAPSTONE_PRIMER.md) | Background on RISC-V, Sail, Ibex, RVFI, riscv-formal and the Ibex ⇔ Sail proof: what each check actually verifies |
| [docs/CAPSTONE_IBEX.md](docs/CAPSTONE_IBEX.md) | Whether an Ibex capstone is feasible, and the three-track plan |
| [docs/CAPSTONE_EXAM_PREP.md](docs/CAPSTONE_EXAM_PREP.md) | Chapters E5–E11: what you need to verify the rest of Ibex yourself (invariants, induction over time, non-interference, refinement, Track 1 practical, Track 3 outline), then the exam |
| [docs/REFERENCES.md](docs/REFERENCES.md) | Third-party projects, licences, bibliography |
