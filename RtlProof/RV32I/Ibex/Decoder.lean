import RtlProof.Generated.IbexDec
import RtlProof.RV32I.Ibex.Alu
import Std.Tactic.BVDecide

/-!
# Ibex decoder vs. the RV32I spec, and decoder + ALU together (capstone Track 2)

`Gen.IbexDec` is generated from lowRISC Ibex's `rtl/ibex_decoder.sv` in a plain
RV32I configuration: `RV32M = RV32MNone`, `RV32B = RV32BNone`,
`BaseIsa = BaseIsaRV32I`. It has 219 cells, and its constant-`x` defaults
become arbitrary inputs.

For every 32-bit instruction word `w` and every value of the other decoder
inputs, assuming only that both copies of the instruction register hold `w`
(Ibex duplicates it to ease fan-out) and that the compressed decoder did not
flag it:

* `decode_op` / `decode_op_imm`: a legal OP / OP-IMM instruction is accepted,
  selects the ALU operation the spec prescribes, takes its operands from rs1
  and rs2 (or the sign-extended I-immediate), writes rd from the ALU result,
  and makes no memory request.
* `decode_op_illegal` / `decode_op_imm_illegal`: reserved `funct7` encodings
  are rejected.
* `decode_branch`: in a branch's first cycle the ALU is set up to compute the
  spec's comparison on rs1 and rs2.

`op_executes` / `op_imm_executes` then chain the decoder theorem with the ALU
theorem (`Alu.lean`): feed the decoder's chosen operation and operands to the
ALU, and the value written to rd is exactly what the spec says.
-/

namespace RtlProof.Ibex
open RV32I

/-- Encodings of the decoder's operand-select outputs (`ibex_pkg.sv`). -/
def OP_A_REG_A : BitVec 2 := 0
def OP_B_REG_B : BitVec 1 := 0
def OP_B_IMM : BitVec 1 := 1
def IMM_B_I : BitVec 3 := 0
def RF_WD_EX : BitVec 1 := 0

/-- What the decoder may assume about its inputs when it sees instruction `w`. -/
structure Fetched (i : Gen.IbexDec.Input) (w : BitVec 32) : Prop where
  rdata : i.instr_rdata_i = w
  rdata_alu : i.instr_rdata_alu_i = w
  not_illegal_c : i.illegal_c_insn_i = 0#1

/-- The ALU operation code the spec prescribes for an OP / OP-IMM instruction. -/
theorem aluOpCode_aluOpOf (w : BitVec 32) :
    aluOpCode (aluOpOf w) =
      (if funct3 w = 0b000#3 then (if opcode w = OPC_OP && funct7 w = 0x20#7 then 1#7 else 0#7)
       else if funct3 w = 0b001#3 then 10#7 else if funct3 w = 0b010#3 then 40#7
       else if funct3 w = 0b011#3 then 41#7 else if funct3 w = 0b100#3 then 2#7
       else if funct3 w = 0b101#3 then (if funct7 w = 0x20#7 then 8#7 else 9#7)
       else if funct3 w = 0b110#3 then 3#7 else 4#7) := by
  simp only [aluOpOf]
  simp only [apply_ite aluOpCode]
  rfl

theorem brOpCode_brOpOf (w : BitVec 32) :
    brOpCode (brOpOf w) =
      (if funct3 w = 0b000#3 then 27#7 else if funct3 w = 0b001#3 then 28#7
       else if funct3 w = 0b100#3 then 23#7 else if funct3 w = 0b101#3 then 25#7
       else if funct3 w = 0b110#3 then 24#7 else 26#7) := by
  simp only [brOpOf]
  simp only [apply_ite brOpCode]
  rfl

/-- **Legal OP instructions.** -/
theorem decode_op (s : Gen.IbexDec.State) (i : Gen.IbexDec.Input) (w : BitVec 32)
    (hf : Fetched i w) (hl : opLegal w = true) :
    let d := Gen.IbexDec.outputs s i
    d.illegal_insn_o = 0#1 ∧ d.alu_operator_o = aluOpCode (aluOpOf w) ∧
    d.alu_op_a_mux_sel_o = OP_A_REG_A ∧ d.alu_op_b_mux_sel_o = OP_B_REG_B ∧
    d.rf_raddr_a_o = rs1Field w ∧ d.rf_raddr_b_o = rs2Field w ∧ d.rf_waddr_o = rdField w ∧
    d.rf_we_o = 1#1 ∧ d.rf_wdata_sel_o = RF_WD_EX ∧ d.data_req_o = 0#1 := by
  obtain ⟨h1, h2, h3⟩ := hf
  rw [aluOpCode_aluOpOf]
  simp only [Gen.IbexDec.outputs, Gen.IbexDec.comb, opLegal, opcode, funct3, funct7, rs1Field, rs2Field, rdField,
    OPC_OP, OP_A_REG_A, OP_B_REG_B, RF_WD_EX] at hl ⊢
  bv_decide

/-- **Legal OP-IMM instructions.** -/
theorem decode_op_imm (s : Gen.IbexDec.State) (i : Gen.IbexDec.Input) (w : BitVec 32)
    (hf : Fetched i w) (hl : opImmLegal w = true) :
    let d := Gen.IbexDec.outputs s i
    d.illegal_insn_o = 0#1 ∧ d.alu_operator_o = aluOpCode (aluOpOf w) ∧
    d.alu_op_a_mux_sel_o = OP_A_REG_A ∧ d.alu_op_b_mux_sel_o = OP_B_IMM ∧
    d.imm_b_mux_sel_o = IMM_B_I ∧ d.imm_i_type_o = immI w ∧
    d.rf_raddr_a_o = rs1Field w ∧ d.rf_waddr_o = rdField w ∧
    d.rf_we_o = 1#1 ∧ d.rf_wdata_sel_o = RF_WD_EX ∧ d.data_req_o = 0#1 := by
  obtain ⟨h1, h2, h3⟩ := hf
  rw [aluOpCode_aluOpOf]
  simp only [Gen.IbexDec.outputs, Gen.IbexDec.comb, opImmLegal, opcode, funct3, funct7, rs1Field, rdField, immI,
    OPC_OP, OPC_OP_IMM, OP_A_REG_A, OP_B_IMM, IMM_B_I, RF_WD_EX] at hl ⊢
  bv_decide

/-- **Reserved OP encodings are rejected.** -/
theorem decode_op_illegal (s : Gen.IbexDec.State) (i : Gen.IbexDec.Input) (w : BitVec 32)
    (hf : Fetched i w) (hop : opcode w = OPC_OP) (hl : opLegal w = false) :
    (Gen.IbexDec.outputs s i).illegal_insn_o = 1#1 := by
  obtain ⟨h1, h2, h3⟩ := hf
  simp only [Gen.IbexDec.outputs, Gen.IbexDec.comb, opLegal, opcode, funct3, funct7, OPC_OP] at hop hl ⊢
  bv_decide

/-- **Reserved OP-IMM shift encodings are rejected.** -/
theorem decode_op_imm_illegal (s : Gen.IbexDec.State) (i : Gen.IbexDec.Input) (w : BitVec 32)
    (hf : Fetched i w) (hop : opcode w = OPC_OP_IMM) (hl : opImmLegal w = false) :
    (Gen.IbexDec.outputs s i).illegal_insn_o = 1#1 := by
  obtain ⟨h1, h2, h3⟩ := hf
  simp only [Gen.IbexDec.outputs, Gen.IbexDec.comb, opImmLegal, opcode, funct3, funct7, OPC_OP_IMM] at hop hl ⊢
  bv_decide

/-- **Branches, first cycle:** the ALU compares rs1 with rs2 using the spec's comparison. -/
theorem decode_branch (s : Gen.IbexDec.State) (i : Gen.IbexDec.Input) (w : BitVec 32)
    (hf : Fetched i w) (hl : branchLegal w = true) (hfirst : i.instr_first_cycle_i = 1#1) :
    let d := Gen.IbexDec.outputs s i
    d.illegal_insn_o = 0#1 ∧ d.alu_operator_o = brOpCode (brOpOf w) ∧
    d.alu_op_a_mux_sel_o = OP_A_REG_A ∧ d.alu_op_b_mux_sel_o = OP_B_REG_B ∧
    d.rf_raddr_a_o = rs1Field w ∧ d.rf_raddr_b_o = rs2Field w ∧ d.rf_we_o = 0#1 := by
  obtain ⟨h1, h2, h3⟩ := hf
  rw [brOpCode_brOpOf]
  simp only [Gen.IbexDec.outputs, Gen.IbexDec.comb, branchLegal, opcode, funct3, rs1Field, rs2Field, OPC_BRANCH,
    OP_A_REG_A, OP_B_REG_B] at hl ⊢
  bv_decide

/-! ### Decoder and ALU together -/

/-- **An OP instruction computes the spec result.** Whatever operation the decoder
selects for `w`, the ALU, given that operation and the values of rs1 and rs2, produces
the value the spec writes to rd. -/
theorem op_executes (s : Gen.IbexDec.State) (i : Gen.IbexDec.Input) (w : BitVec 32)
    (hf : Fetched i w) (hl : opLegal w = true)
    (rs1v rs2v : BitVec 32) (ma mb : BitVec 33) (sa : Gen.IbexAlu.State) :
    (Gen.IbexAlu.comb sa (aluIn (Gen.IbexDec.outputs s i).alu_operator_o rs1v rs2v ma mb)).result_o =
      (aluOpOf w).exec rs1v rs2v := by
  rw [(decode_op s i w hf hl).2.1]
  exact alu_result _ _ _ _ _ _

/-- **An OP-IMM instruction computes the spec result**, with the immediate the decoder
produces as the second operand. -/
theorem op_imm_executes (s : Gen.IbexDec.State) (i : Gen.IbexDec.Input) (w : BitVec 32)
    (hf : Fetched i w) (hl : opImmLegal w = true)
    (rs1v : BitVec 32) (ma mb : BitVec 33) (sa : Gen.IbexAlu.State) :
    let d := Gen.IbexDec.outputs s i
    (Gen.IbexAlu.comb sa (aluIn d.alu_operator_o rs1v d.imm_i_type_o ma mb)).result_o =
      (aluOpOf w).exec rs1v (immI w) := by
  have h := decode_op_imm s i w hf hl
  simp only at h ⊢
  rw [h.2.1, h.2.2.2.2.2.1]
  exact alu_result _ _ _ _ _ _

end RtlProof.Ibex
