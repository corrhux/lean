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
| M0 skeleton | Lake project (`lakefile.toml`, Lean 4.36.0), Python package, CI, Docker image and dev container are in place. **Lean files not yet compiled** (see below). |
| M1 Lean core | `RtlProof/Core/Circuit.lean` (semantics) and `RtlProof/Meta/Induction.lean` (induction soundness) are written. k-induction soundness is still to do. |
| M3 satlab | **Working and tested**: teaching DPLL/CDCL with traces, generators, solver zoo (including CaDiCaL and Kissat), DRUP proof checking. See [satlab/README.md](satlab/README.md). |
| RTL | `rtl/counter`: BMC, k-induction, cover and bug tasks pass with SymbiYosys. See [rtl/counter/README.md](rtl/counter/README.md). |

The Lean files and the Lean course code have not been compiled yet, because
the Lean toolchain could not be run in the cloud session that wrote them. CI's
`lean` job, or `lake build` in the dev container, is the first check.

## Quick start

```sh
pip install -e ".[dev]" && pytest          # satlab
satlab gen mul-miter --width 8 -o m8.cnf && satlab zoo m8.cnf
lake build                                 # Lean library (needs elan)
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
