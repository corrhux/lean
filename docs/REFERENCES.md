# References and third-party projects

Licences and URLs marked **(verify)** must be confirmed against the pinned
version during M0's licence audit. Nothing here is copied into this repo;
third-party code is pulled as pinned submodules or installed packages.

## Third-party software

| Project | Use | Licence |
|---|---|---|
| Lean 4 / Lake (leanprover/lean4) | Prover | Apache-2.0 |
| ProofWidgets4 | Infoview widgets | Apache-2.0 (verify) |
| Mathlib4 (deferred) | Algebra library | Apache-2.0 |
| lean4web / `@leanprover/infoview` | Web goal view | Apache-2.0 (verify) |
| Yosys | Elaboration, export, sim | ISC |
| yosys-slang (+ slang) | SystemVerilog frontend | (verify) |
| sv2v | SV → Verilog | BSD-3-Clause (verify) |
| SymbiYosys | Formal task runner | ISC |
| ABC (Berkeley) | pdr, bmc3, sweeping | BSD-style (verify) |
| rIC3 | IC3/PDR engine | (verify) |
| Pono (optional) | Word-level MC | BSD-3-Clause (verify) |
| CaDiCaL, Kissat | SAT solvers | MIT |
| PySAT | Solver zoo | MIT |
| Z3 | SMT | MIT |
| Bitwuzla | BV SMT | MIT (verify) |
| cvc5 (optional) | SMT | BSD-3-Clause |
| drat-trim, lrat-check | Proof checkers | (verify) |
| Surfer | Waveform viewer | EUPL-1.2 (verify) |
| mdBook | Course book | MPL-2.0 |
| lowRISC Ibex | Capstone DUT | Apache-2.0 |
| riscv-formal | RVFI checks | ISC |
| sail-riscv, Sail | ISA spec, emulator, Sail→Lean | BSD-2-Clause (verify) |
| Verilator | Ibex simulation (E0 labs) | LGPL-3.0 / Artistic-2.0 (verify) |
| RISC-V GNU toolchain | Compile lab ELFs | GPL (tool only, not linked) (verify) |
| Anthropic Python SDK | Tutor | MIT (verify) |

## Ibex / capstone sources
- lowRISC, *Open Source Correctness Proof for Ibex* — https://lowrisc.org/news/open-source-correctness-proof-for-ibex/
- FOSSi Foundation news item on the open Ibex proof — https://librecores.org/blog/2026-02-21-ecl94
- *Comprehensive Formal Verification of Observational Correctness for the CHERIoT-Ibex Processor* — https://arxiv.org/abs/2502.04738
- lowRISC, *Groundbreaking Formal Verification Further Enhances the Quality of CHERIoT-Ibex* — https://lowrisc.org/news/groundbreaking-formal-verification-further-enhances-the-quality-of-cheriot-ibex/
- Oxford CS news on CHERIoT-Ibex verification — https://www.cs.ox.ac.uk/news/2417-full.html
- L.-E. Ploix, *Crossing the Model Checking / Theorem Proving Gap for Ibex Correctness*, DVClub Cambridge 2025 — https://alpinumconsulting.com/wp-content/uploads/Louis-Emile-Ploix-Crossing-the-Model-CheckingTheorem-Proving-Gap-for-Ibex-Correctness.pdf
- Ibex configuration docs — https://ibex-core.readthedocs.io/en/latest/02_user/configuration.html
- Ibex `formal/` (riscv-formal via sv2v + Yosys) and `syn/` flows — in the Ibex repository
- sail-riscv — https://github.com/riscv/sail-riscv (Lean backend: confirm status with Sail compiler docs)
- Armstrong et al., *ISA Semantics for ARMv8-A, RISC-V, and CHERI-MIPS*, POPL 2019 (Sail).
- riscv-formal / RVFI — https://github.com/YosysHQ/riscv-formal
- RISC-V Unprivileged and Privileged ISA specifications — https://riscv.org/specifications/
- Ibex `examples/simple_system` and `ibex_tracer` — in the Ibex repository

## Lean
- *Theorem Proving in Lean 4*; *Functional Programming in Lean*; *Mathematics in Lean*;
  *The Hitchhiker's Guide to Logical Verification*; Lean reference manual (`bv_decide`, `grind`).
- LeanSAT / `bv_decide` system paper (Lean FRO) (verify exact citation).

## SAT / SMT
- Davis & Putnam 1960; Davis, Logemann & Loveland 1962.
- Marques-Silva & Sakallah, GRASP, 1996/1999.
- Moskewicz et al., Chaff, DAC 2001.
- Eén & Sörensson, *An Extensible SAT-solver* (MiniSat), SAT 2003.
- Eén & Biere, SatELite preprocessing, SAT 2005.
- Audemard & Simon, Glucose / LBD, IJCAI 2009.
- Soos et al., CryptoMiniSat, SAT 2009.
- Liang et al., Learning-rate branching (MapleSAT), SAT 2016.
- Biere et al., CaDiCaL / Kissat system descriptions, SAT Competition 2017–.
- Biere, Heule, van Maaren, Walsh (eds.), *Handbook of Satisfiability*, 2nd ed., 2021.
- Brummayer & Biere, Boolector; Niemetz & Preiner, Bitwuzla (CAV 2023).

## Model checking
- Biere, Cimatti, Clarke, Zhu, *Symbolic Model Checking without BDDs*, TACAS 1999.
- Sheeran, Singh, Stålmarck, *Checking Safety Properties Using Induction and a SAT-Solver*, FMCAD 2000.
- McMillan, *Interpolation and SAT-based Model Checking*, CAV 2003.
- Bradley, *SAT-Based Model Checking without Unrolling*, VMCAI 2011.
- Eén, Mishchenko, Brayton, *Efficient Implementation of Property Directed Reachability*, FMCAD 2011.
- McMillan, *Symbolic Model Checking*, 1993 (SMV).

## Proof certificates
- Wetzler, Heule, Hunt, *DRAT-trim*, SAT 2014.
- Cruz-Filipe, Heule, Hunt, Kaufmann, Schneider-Kamp, *Efficient Certified RAT Verification* (LRAT), CADE 2017.
- Heule, Hunt, Kaufmann, Wetzler, *Efficient, Verified Checking of Propositional Proofs*, ITP 2017.
- Baek, Carneiro, Heule, *A Flexible Proof Format for SAT Solver-Elaborator Communication* (FRAT), TACAS 2021.
- Tan, Heule, Myreen, *cake_lpr: Verified Propagation Redundancy Checking in CakeML*, TACAS 2021.

## Theorem provers × SAT
- Weber, *Integrating a SAT Solver with an LCF-style Theorem Prover*, PDPAR 2005 (verify).
- Weber & Amjad, *Efficiently Checking Propositional Refutations in HOL Theorem Provers*, JAL 2009.
- Böhme & Weber, *Fast LCF-Style Proof Reconstruction for Z3*, ITP 2010.
- Paulson & Blanchette, Sledgehammer papers, 2007–.
- Armand et al., *A Modular Integration of SAT/SMT Solvers to Coq through Proof Witnesses* (SMTCoq), CPP 2011.
- Besson, *Itauto: An Extensible Intuitionistic SAT Solver*, ITP 2021.
- Davis & Swords, *Verified AIG Algorithms in ACL2* / SATLINK, ACL2 Workshop 2013.

## History and hardware ITP
- Gordon, *From LCF to HOL: a short history*, 2000.
- Milner, LCF papers (1972, 1979).
- Moore, Lynch, Kaufmann, *A Mechanically Checked Proof of the AMD5K86 Floating-Point Division Program*, IEEE TC 1998.
- Seger et al., *An Industrially Effective Environment for Formal Hardware Verification* (Forte), IEEE TCAD 2005.
- Hunt, Swords, Davis et al., Centaur x86 verification with ACL2 (GL).
- Harrison, *Handbook of Practical Logic and Automated Reasoning*, 2009.
- MacKenzie, *Mechanizing Proof*, MIT Press 2001.
