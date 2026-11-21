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

Status: **specification and architecture stage.** No implementation yet.

| Document | Contents |
|---|---|
| [docs/SPEC.md](docs/SPEC.md) | Goals, workflows, requirements, milestones |
| [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md) | Components, repo layout, toolchain, interfaces, CI, design decisions |
| [docs/COURSE.md](docs/COURSE.md) | Full syllabus, Parts A–E, including the SAT and history chapters |
| [docs/CAPSTONE_PRIMER.md](docs/CAPSTONE_PRIMER.md) | Background on RISC-V, Sail, Ibex, RVFI, riscv-formal and the Ibex ⇔ Sail proof: what each check actually verifies |
| [docs/CAPSTONE_IBEX.md](docs/CAPSTONE_IBEX.md) | Whether an Ibex capstone is feasible, and the three-track plan |
| [docs/REFERENCES.md](docs/REFERENCES.md) | Third-party projects, licences, bibliography |
