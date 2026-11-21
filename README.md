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
| M2 sv2lean | **Working**: SystemVerilog → Yosys → Lean (`tools/sv2lean`). Differential-tested against Yosys's own semantics; mutation tests show the difftest catches injected bugs. |
| `ftwin` | `ftwin run <design>`: SymbiYosys tasks and Lean theorems side by side (`tools/ftwin`). |
| M6 tutor | `tutor ask/chat` (`tools/tutor`): Claude explains in Jasper terms on a 5-level hint ladder, with tools to compile Lean, look up course sections, read files, summarise counterexample waveforms and run twins. Tools are tested offline; the live API path needs `ANTHROPIC_API_KEY`. |
| M5 Ibex capstone | **Started.** lowRISC Ibex pinned as a submodule. Track 2: Ibex's ALU (every RV32I operation and branch comparison), decoder (every OP/OP-IMM/branch instruction) and compressed decoder (all 49,152 compressed encodings) are proven against a Lean RV32I/RV32C spec written from the ISA manual, and decoder + ALU are composed into instruction-level theorems. See [capstone/ibex/README.md](capstone/ibex/README.md). |
| Twin labs | `rtl/counter`, `rtl/mul`, `rtl/fifo`, `rtl/arbiter`: each proven on both sides. Lean proves the **multiplier algorithm for every width**, the **FIFO control for every depth** and **round-robin fairness for every N**, then links each to the generated RTL. Measured scaling is in each design's README. `ftwin bench <design>` sweeps the parameter. |
| M1b Lean fluency | All 48 code blocks in [docs/LEAN_FLUENCY.md](docs/LEAN_FLUENCY.md) compile on Lean 4.36.0, and the 3 intentional failures fail (`tools/lean_blocks.py`, run in CI). |
| M3 satlab | **Working and tested**: teaching DPLL/CDCL with traces, generators, solver zoo (including CaDiCaL and Kissat), DRUP proof checking. See [satlab/README.md](satlab/README.md). |
| RTL | `rtl/counter`: BMC, k-induction, cover and bug tasks pass with SymbiYosys. See [rtl/counter/README.md](rtl/counter/README.md). |

## Quick start

```sh
pip install -e ".[dev]" && pytest          # satlab
satlab gen mul-miter --width 8 -o m8.cnf && satlab zoo m8.cnf
lake build                                 # Lean library (needs elan)
ftwin run counter                          # both sides of the counter twin
sv2lean rtl/counter/counter.sv --top counter --difftest 10   # Lean model vs Yosys
cd rtl/counter && sby -f counter.sby       # needs the OSS CAD Suite
```

Or open the repo in the dev container (`.devcontainer/`), which installs Lean,
the OSS CAD Suite and the Python tools.

## Documents

| Document | Contents |
|---|---|
| [docs/SPEC.md](docs/SPEC.md) | Goals, workflows, requirements, milestones |
| [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md) | Components, repo layout, toolchain, interfaces, CI, design decisions |
| [docs/COURSE.md](docs/COURSE.md) | Full syllabus, Parts A–E, including the SAT and history chapters |
| [docs/LEAN_FLUENCY.md](docs/LEAN_FLUENCY.md) | Course Part C: the Lean language and its semantics in plain terms, in 18 lessons with RTL/Jasper analogies, drills and solutions |
| [docs/CAPSTONE_PRIMER.md](docs/CAPSTONE_PRIMER.md) | Background on RISC-V, Sail, Ibex, RVFI, riscv-formal and the Ibex ⇔ Sail proof: what each check actually verifies |
| [docs/CAPSTONE_IBEX.md](docs/CAPSTONE_IBEX.md) | Whether an Ibex capstone is feasible, and the three-track plan |
| [docs/REFERENCES.md](docs/REFERENCES.md) | Third-party projects, licences, bibliography |
