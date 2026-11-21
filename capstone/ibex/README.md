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
| `ibex_decoder` | `RV32M = None`, `RV32B = None`, `BaseIsa = RV32I` | `Gen.IbexDec`: 219 cells | for **every** 32-bit instruction: legal OP/OP-IMM are accepted with the spec's ALU operation, operand sources (rs1, rs2 or the sign-extended I-immediate), rd write-back and no memory request; reserved `funct7`/shift encodings are rejected; branches set the ALU to the spec's comparison | `RtlProof/RV32I/Ibex/Decoder.lean` |
| **decoder + ALU** | as above | both models | `op_executes`, `op_imm_executes`: for every legal OP / OP-IMM instruction and all register values, the ALU result the decoder sets up is the value the spec writes to rd | `RtlProof/RV32I/Ibex/Decoder.lean` |
| **loads, stores, jumps** | as above | both models | LB/LH/LW/LBU/LHU and SB/SH/SW: legal encodings accepted (others rejected), memory request with the right size, write flag and sign extension, rs1/rs2/rd routing, and **the ALU computes the spec's address `rs1 + imm`**. JAL/JALR: first cycle computes the spec's target (`pc + immJ`, `rs1 + immI`) and requests the jump; second cycle computes the link value and writes rd. Branches: second cycle computes `pc + immB` when taken. | `RtlProof/RV32I/Ibex/LoadStoreJump.lean` |
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
* **More Track 2 blocks:** LUI/AUIPC and SYSTEM (CSR, ECALL/EBREAK, MRET,
  WFI, FENCE) in the decoder; the load/store unit (byte lanes, sign extension,
  misaligned splitting); the register file; `ibex_multdiv_slow` (needs a
  sequential invariant).
* **Covered by other parts of Ibex, not yet proven:** the `IMM_B_INCR_PC`
  immediate is 4 (or 2 after a compressed instruction) in `ibex_id_stage`;
  JALR's clearing of target bit 0 happens on the way to the fetch stage.
* **Assumptions to discharge later:** the decoder proofs assume both copies of
  the instruction register (`instr_rdata_i`, `instr_rdata_alu_i`) hold the
  same word. That is a fact about `ibex_id_stage`/`ibex_if_stage`, which a
  pipeline-level proof (Track 3) would show.
* **Track 3:** the pipeline slice refinement.
