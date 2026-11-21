import RtlProof.RV32I.Ibex.Decoder
import Std.Tactic.BVDecide

/-!
# Ibex: loads, stores, jumps and branch targets vs. the RV32I spec

Same setting as `Decoder.lean`: every 32-bit instruction word, every other
decoder input arbitrary, both instruction-register copies equal.

How Ibex executes these (the claims below are checked, not assumed):

* **Loads/stores**: the ALU's adder computes the address `rs1 + imm`
  (`adder_result_o`), and the decoder issues a data-memory request with the
  access size (and, for loads, sign extension). Load data reaches rd through
  the load/store unit; `rf_we_or_load_o` marks that rd will be written.
* **JAL/JALR** take two cycles (with `BranchTargetALU = 0`). The first cycle
  computes the target in the ALU (`pc + immJ`, or `rs1 + immI`) and sets
  `jump_set_o`. The second computes the link value `pc + 4` (the
  `IMM_B_INCR_PC` immediate) and writes rd. JALR's clearing of target bit 0
  happens outside the decoder and is not covered here.
* **Branches**: after the first-cycle comparison (`decode_branch` in
  Decoder.lean), the second cycle computes `pc + immB` if taken, else
  `pc + 4`.

`adder_sum` (the ALU adder with `ALU_ADD` adds) turns each decoder setup into
the spec's address or target.
-/

namespace RtlProof.Ibex
open RV32I

/-- More of the decoder's selector encodings (`ibex_pkg.sv`). -/
def OP_A_CURRPC : BitVec 2 := 2
def IMM_B_S : BitVec 3 := 1
def IMM_B_B : BitVec 3 := 2
def IMM_B_J : BitVec 3 := 4
def IMM_B_INCR_PC : BitVec 3 := 5
def ALU_ADD : BitVec 7 := 0

/-- Ibex's `data_type_o` encoding of access sizes. -/
def sizeCode : Size → BitVec 2
  | .word => 0 | .half => 1 | .byte => 2

theorem sizeCode_sizeOf (w : BitVec 32) :
    sizeCode (accessSize w) =
      (if (funct3 w).extractLsb 1 0 = 0b00#2 then 2#2
       else if (funct3 w).extractLsb 1 0 = 0b01#2 then 1#2 else 0#2) := by
  simp only [accessSize]
  simp only [apply_ite sizeCode]
  rfl

/-- **The ALU adder adds**: with `ALU_ADD`, `adder_result_o = a + b`, for all operands.
The load/store unit uses this output as the memory address. -/
theorem adder_sum (a b : BitVec 32) (ma mb : BitVec 33) (s : Gen.IbexAlu.State) :
    (Gen.IbexAlu.outputs s (aluIn ALU_ADD a b ma mb)).adder_result_o = a + b := by
  simp only [Gen.IbexAlu.outputs, Gen.IbexAlu.comb, aluIn, ALU_ADD]
  bv_decide

/-! ### Loads -/

theorem decode_load (s : Gen.IbexDec.State) (i : Gen.IbexDec.Input) (w : BitVec 32)
    (hf : Fetched i w) (hl : loadLegal w = true) :
    let d := Gen.IbexDec.outputs s i
    d.illegal_insn_o = 0#1 ∧ d.data_req_o = 1#1 ∧ d.data_we_o = 0#1 ∧
    d.data_type_o = sizeCode (accessSize w) ∧ d.data_sign_extension_o = BitVec.ofBool (loadSigned w) ∧
    d.rf_raddr_a_o = rs1Field w ∧ d.rf_waddr_o = rdField w ∧ d.rf_we_or_load_o = 1#1 ∧
    d.alu_operator_o = ALU_ADD ∧ d.alu_op_a_mux_sel_o = OP_A_REG_A ∧
    d.alu_op_b_mux_sel_o = OP_B_IMM ∧ d.imm_b_mux_sel_o = IMM_B_I ∧ d.imm_i_type_o = immI w := by
  obtain ⟨h1, h2, h3⟩ := hf
  rw [sizeCode_sizeOf]
  simp only [Gen.IbexDec.outputs, Gen.IbexDec.comb, loadLegal, loadSigned, opcode, funct3,
    rs1Field, rdField, immI, OPC_LOAD, ALU_ADD, OP_A_REG_A, OP_B_IMM, IMM_B_I] at hl ⊢
  bv_decide

theorem decode_load_illegal (s : Gen.IbexDec.State) (i : Gen.IbexDec.Input) (w : BitVec 32)
    (hf : Fetched i w) (hop : opcode w = OPC_LOAD) (hl : loadLegal w = false) :
    (Gen.IbexDec.outputs s i).illegal_insn_o = 1#1 := by
  obtain ⟨h1, h2, h3⟩ := hf
  simp only [Gen.IbexDec.outputs, Gen.IbexDec.comb, loadLegal, opcode, funct3, OPC_LOAD] at hop hl ⊢
  bv_decide

/-- **Load address**: what the ALU computes from the decoder's setup is the spec's address. -/
theorem load_address (s : Gen.IbexDec.State) (i : Gen.IbexDec.Input) (w : BitVec 32)
    (hf : Fetched i w) (hl : loadLegal w = true)
    (rs1v : BitVec 32) (ma mb : BitVec 33) (sa : Gen.IbexAlu.State) :
    let d := Gen.IbexDec.outputs s i
    (Gen.IbexAlu.outputs sa (aluIn d.alu_operator_o rs1v d.imm_i_type_o ma mb)).adder_result_o =
      loadAddr w rs1v := by
  have h := decode_load s i w hf hl
  simp only at h ⊢
  rw [h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2, adder_sum]
  rfl

/-! ### Stores -/

theorem decode_store (s : Gen.IbexDec.State) (i : Gen.IbexDec.Input) (w : BitVec 32)
    (hf : Fetched i w) (hl : storeLegal w = true) :
    let d := Gen.IbexDec.outputs s i
    d.illegal_insn_o = 0#1 ∧ d.data_req_o = 1#1 ∧ d.data_we_o = 1#1 ∧
    d.data_type_o = sizeCode (accessSize w) ∧
    d.rf_raddr_a_o = rs1Field w ∧ d.rf_raddr_b_o = rs2Field w ∧
    d.rf_we_o = 0#1 ∧ d.rf_we_or_load_o = 0#1 ∧
    d.alu_operator_o = ALU_ADD ∧ d.alu_op_a_mux_sel_o = OP_A_REG_A ∧
    d.alu_op_b_mux_sel_o = OP_B_IMM ∧ d.imm_b_mux_sel_o = IMM_B_S ∧ d.imm_s_type_o = immS w := by
  obtain ⟨h1, h2, h3⟩ := hf
  rw [sizeCode_sizeOf]
  simp only [Gen.IbexDec.outputs, Gen.IbexDec.comb, storeLegal, opcode, funct3, rs1Field,
    rs2Field, immS, OPC_STORE, ALU_ADD, OP_A_REG_A, OP_B_IMM, IMM_B_S] at hl ⊢
  bv_decide

theorem decode_store_illegal (s : Gen.IbexDec.State) (i : Gen.IbexDec.Input) (w : BitVec 32)
    (hf : Fetched i w) (hop : opcode w = OPC_STORE) (hl : storeLegal w = false) :
    (Gen.IbexDec.outputs s i).illegal_insn_o = 1#1 := by
  obtain ⟨h1, h2, h3⟩ := hf
  simp only [Gen.IbexDec.outputs, Gen.IbexDec.comb, storeLegal, opcode, funct3, OPC_STORE]
    at hop hl ⊢
  bv_decide

theorem store_address (s : Gen.IbexDec.State) (i : Gen.IbexDec.Input) (w : BitVec 32)
    (hf : Fetched i w) (hl : storeLegal w = true)
    (rs1v : BitVec 32) (ma mb : BitVec 33) (sa : Gen.IbexAlu.State) :
    let d := Gen.IbexDec.outputs s i
    (Gen.IbexAlu.outputs sa (aluIn d.alu_operator_o rs1v d.imm_s_type_o ma mb)).adder_result_o =
      storeAddr w rs1v := by
  have h := decode_store s i w hf hl
  simp only at h ⊢
  rw [h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2, adder_sum]
  rfl

/-! ### Jumps -/

/-- **JAL, first cycle**: the ALU computes `pc + immJ` and the jump is requested. -/
theorem decode_jal_target (s : Gen.IbexDec.State) (i : Gen.IbexDec.Input) (w : BitVec 32)
    (hf : Fetched i w) (hl : jalLegal w = true) (hfirst : i.instr_first_cycle_i = 1#1) :
    let d := Gen.IbexDec.outputs s i
    d.illegal_insn_o = 0#1 ∧ d.jump_in_dec_o = 1#1 ∧ d.jump_set_o = 1#1 ∧ d.rf_we_o = 0#1 ∧
    d.alu_operator_o = ALU_ADD ∧ d.alu_op_a_mux_sel_o = OP_A_CURRPC ∧
    d.alu_op_b_mux_sel_o = OP_B_IMM ∧ d.imm_b_mux_sel_o = IMM_B_J ∧ d.imm_j_type_o = immJ w := by
  obtain ⟨h1, h2, h3⟩ := hf
  simp only [Gen.IbexDec.outputs, Gen.IbexDec.comb, jalLegal, opcode, immJ, OPC_JAL, ALU_ADD,
    OP_A_CURRPC, OP_B_IMM, IMM_B_J] at hl ⊢
  bv_decide

/-- **JALR, first cycle**: the ALU computes `rs1 + immI` and the jump is requested. -/
theorem decode_jalr_target (s : Gen.IbexDec.State) (i : Gen.IbexDec.Input) (w : BitVec 32)
    (hf : Fetched i w) (hl : jalrLegal w = true) (hfirst : i.instr_first_cycle_i = 1#1) :
    let d := Gen.IbexDec.outputs s i
    d.illegal_insn_o = 0#1 ∧ d.jump_in_dec_o = 1#1 ∧ d.jump_set_o = 1#1 ∧ d.rf_we_o = 0#1 ∧
    d.rf_raddr_a_o = rs1Field w ∧ d.alu_operator_o = ALU_ADD ∧
    d.alu_op_a_mux_sel_o = OP_A_REG_A ∧ d.alu_op_b_mux_sel_o = OP_B_IMM ∧
    d.imm_b_mux_sel_o = IMM_B_I ∧ d.imm_i_type_o = immI w := by
  obtain ⟨h1, h2, h3⟩ := hf
  simp only [Gen.IbexDec.outputs, Gen.IbexDec.comb, jalrLegal, opcode, funct3, rs1Field, immI,
    OPC_JALR, ALU_ADD, OP_A_REG_A, OP_B_IMM, IMM_B_I] at hl ⊢
  bv_decide

/-- **JAL and JALR, second cycle**: the ALU computes the link value `pc + increment`
and rd is written. -/
theorem decode_jump_link (s : Gen.IbexDec.State) (i : Gen.IbexDec.Input) (w : BitVec 32)
    (hf : Fetched i w) (hl : jalLegal w = true ∨ jalrLegal w = true)
    (hsecond : i.instr_first_cycle_i = 0#1) :
    let d := Gen.IbexDec.outputs s i
    d.illegal_insn_o = 0#1 ∧ d.rf_we_o = 1#1 ∧ d.rf_waddr_o = rdField w ∧ d.jump_set_o = 0#1 ∧
    d.alu_operator_o = ALU_ADD ∧ d.alu_op_a_mux_sel_o = OP_A_CURRPC ∧
    d.alu_op_b_mux_sel_o = OP_B_IMM ∧ d.imm_b_mux_sel_o = IMM_B_INCR_PC := by
  obtain ⟨h1, h2, h3⟩ := hf
  simp only [Gen.IbexDec.outputs, Gen.IbexDec.comb, jalLegal, jalrLegal, opcode, funct3, rdField,
    OPC_JAL, OPC_JALR, ALU_ADD, OP_A_CURRPC, OP_B_IMM, IMM_B_INCR_PC] at hl ⊢
  bv_decide

theorem decode_jalr_illegal (s : Gen.IbexDec.State) (i : Gen.IbexDec.Input) (w : BitVec 32)
    (hf : Fetched i w) (hop : opcode w = OPC_JALR) (hl : jalrLegal w = false) :
    (Gen.IbexDec.outputs s i).illegal_insn_o = 1#1 := by
  obtain ⟨h1, h2, h3⟩ := hf
  simp only [Gen.IbexDec.outputs, Gen.IbexDec.comb, jalrLegal, opcode, funct3, OPC_JALR]
    at hop hl ⊢
  bv_decide

/-- **JAL target**: what the ALU computes in the first cycle is the spec's target. -/
theorem jal_target (s : Gen.IbexDec.State) (i : Gen.IbexDec.Input) (w : BitVec 32)
    (hf : Fetched i w) (hl : jalLegal w = true) (hfirst : i.instr_first_cycle_i = 1#1)
    (pc : BitVec 32) (ma mb : BitVec 33) (sa : Gen.IbexAlu.State) :
    let d := Gen.IbexDec.outputs s i
    (Gen.IbexAlu.outputs sa (aluIn d.alu_operator_o pc d.imm_j_type_o ma mb)).adder_result_o =
      jalTarget w pc := by
  have h := decode_jal_target s i w hf hl hfirst
  simp only at h ⊢
  rw [h.2.2.2.2.1, h.2.2.2.2.2.2.2.2, adder_sum]
  rfl

/-! ### Branches, second cycle -/

/-- **Branch target**: if taken, the ALU computes `pc + immB`; if not, `pc + increment`. -/
theorem decode_branch_target (s : Gen.IbexDec.State) (i : Gen.IbexDec.Input) (w : BitVec 32)
    (hf : Fetched i w) (hl : branchLegal w = true) (hsecond : i.instr_first_cycle_i = 0#1) :
    let d := Gen.IbexDec.outputs s i
    d.illegal_insn_o = 0#1 ∧ d.alu_operator_o = ALU_ADD ∧ d.alu_op_a_mux_sel_o = OP_A_CURRPC ∧
    d.alu_op_b_mux_sel_o = OP_B_IMM ∧ d.imm_b_type_o = immB w ∧
    d.imm_b_mux_sel_o = (if i.branch_taken_i = 1#1 then IMM_B_B else IMM_B_INCR_PC) := by
  obtain ⟨h1, h2, h3⟩ := hf
  simp only [Gen.IbexDec.outputs, Gen.IbexDec.comb, branchLegal, opcode, funct3, immB, OPC_BRANCH,
    ALU_ADD, OP_A_CURRPC, OP_B_IMM, IMM_B_B, IMM_B_INCR_PC] at hl ⊢
  bv_decide

end RtlProof.Ibex
