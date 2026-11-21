# Ibex capstone

lowRISC Ibex, the RISC-V core in OpenTitan, is pinned as a submodule at
`third_party/ibex` (commit `041098fe`, 2026-11-20):

```sh
git submodule update --init third_party/ibex
```

Plan and background: [docs/CAPSTONE_IBEX.md](../../docs/CAPSTONE_IBEX.md) and
[docs/CAPSTONE_PRIMER.md](../../docs/CAPSTONE_PRIMER.md).

## Track 2: Lean proofs on Ibex blocks (done so far)

| Block | Configuration | Lean model | Proven | File |
|---|---|---|---|---|
| `ibex_alu` | `RV32B = RV32BNone` | `Gen.IbexAlu`: 124 cells | every RV32I ALU operation (ADD … AND, 10 ops) gives the spec result, and every branch comparison (6) agrees with the spec, for **all** operands | `RtlProof/RV32I/Ibex/Alu.lean` |
| `ibex_compressed_decoder` | `RV32ZC = RV32Zca`, `BaseIsa = RV32I` | `Gen.IbexCDec`: 63 cells | for **all** 49,152 compressed encodings: illegal exactly when the spec says so, and every legal one expands to the spec's 32-bit instruction; 32-bit instructions pass through | `RtlProof/RV32I/Ibex/CDec.lean` |

The spec (`RtlProof/RV32I/Spec.lean`, `RtlProof/RV32I/Compressed.lean`) is
written from the RISC-V Unprivileged ISA manual, independently of Ibex's RTL.
The two agreed on the first run. As a check that the comparison has teeth,
swapping two `C.ADDI4SPN` immediate bits, or forgetting that `C.LWSP` with
`rd = x0` is reserved, each produces a counterexample instruction. Every proof
is one `bv_decide` call per case and takes seconds.

Assumption in the ALU proofs: `multdiv_sel_i = 0`. That input hands the adder
to the multiply/divide unit, which the decoder only does for M-extension
instructions.

## How the models are made

Ibex's SystemVerilog uses packages, assignment patterns and `unique case`,
which Yosys's built-in parser rejects. As Ibex's own synthesis and LEC flows
do, the files go through **sv2v** first:

```sh
capstone/ibex/generate.sh             # regenerate RtlProof/Generated/Ibex*.lean
capstone/ibex/generate.sh --difftest  # and compare each model with Yosys on random inputs
```

Two translator decisions matter for these blocks, and both match Yosys's
formal backends (so the Lean models agree with SymbiYosys on every input):

* **Violated `unique case`** (several case arms active, e.g. `multdiv_sel_i`
  together with a comparison in the ALU) becomes a `$pmux` cell with several
  active selects. Yosys's `sat` and SMT2 backends let the **last** active arm
  win, and so does sv2lean.
* **`x` defaults** (the arm taken when no case matches) become unconstrained
  inputs `undef_k`, so every proof has to hold whatever value the hardware
  produces there.

## Not done yet

* **Track 1** (riscv-formal via RVFI; lowRISC's Sail-equivalence proof in
  `third_party/ibex/dv/formal`) needs the native OSS CAD Suite with
  yosys-slang, rIC3 and the Sail compiler. None of these run in the
  WebAssembly toolchain used here; the dev container image installs the CAD
  suite.
* **More Track 2 blocks:** `ibex_decoder` (RV32I subset), the register file,
  `ibex_multdiv_slow` (needs a sequential invariant).
* **Track 3:** the pipeline slice refinement.
