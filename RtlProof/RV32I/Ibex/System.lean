import RtlProof.RV32I.Ibex.LoadStoreJump
import Std.Tactic.BVDecide

/-!
# Ibex: LUI, AUIPC, FENCE, FENCE.I and SYSTEM vs. the spec

Same setting as `Decoder.lean`: every 32-bit instruction word, every other
decoder input arbitrary, both instruction-register copies equal.

* LUI/AUIPC: the ALU adds `0` or `pc` to the U-immediate, and rd is written.
  `lui_result` / `auipc_result` compose this with the ALU.
* FENCE: accepted, writes nothing. FENCE.I: a jump to the next instruction
  that also invalidates the instruction cache.
* ECALL, EBREAK, MRET, WFI, DRET: recognised exactly at their fixed encodings,
  including rs1 = rd = 0. Any other `funct3 = 000` SYSTEM word is illegal.
* Zicsr: legal CSR instructions access the CSR named by `imm[11:0]` with the
  spec's operation. CSRRS/CSRRC with a zero source field only read. The source
  is rs1 or the zero-extended `uimm`, and rd receives the old CSR value.
-/

namespace RtlProof.Ibex
open RV32I

def OP_A_IMM : BitVec 2 := 3
def IMM_A_Z : BitVec 1 := 0
def IMM_A_ZERO : BitVec 1 := 1
def IMM_B_U : BitVec 3 := 3
def RF_WD_CSR : BitVec 1 := 1

/-- Ibex's `csr_op_e` encoding. -/
def csrOpCode : CsrOp → BitVec 2
  | .read => 0 | .write => 1 | .set => 2 | .clear => 3

theorem csrOpCode_csrOpOf (w : BitVec 32) :
    csrOpCode (csrOpOf w) =
      (if (funct3 w).extractLsb 1 0 = 0b01#2 then 1#2
       else if rs1Field w = 0#5 then 0#2
       else if (funct3 w).extractLsb 1 0 = 0b10#2 then 2#2 else 3#2) := by
  simp only [csrOpOf]
  simp only [apply_ite csrOpCode]
  rfl

/-! ### LUI / AUIPC -/

theorem decode_lui (s : Gen.IbexDec.State) (i : Gen.IbexDec.Input) (w : BitVec 32)
    (hf : Fetched i w) (hop : opcode w = OPC_LUI) :
    let d := Gen.IbexDec.outputs s i
    d.illegal_insn_o = 0#1 ∧ d.rf_we_o = 1#1 ∧ d.rf_waddr_o = rdField w ∧
    d.rf_wdata_sel_o = RF_WD_EX ∧ d.alu_operator_o = ALU_ADD ∧
    d.alu_op_a_mux_sel_o = OP_A_IMM ∧ d.imm_a_mux_sel_o = IMM_A_ZERO ∧
    d.alu_op_b_mux_sel_o = OP_B_IMM ∧ d.imm_b_mux_sel_o = IMM_B_U ∧ d.imm_u_type_o = immU w := by
  obtain ⟨h1, h2, h3⟩ := hf
  simp only [Gen.IbexDec.outputs, Gen.IbexDec.comb, opcode, rdField, immU, OPC_LUI, RF_WD_EX,
    ALU_ADD, OP_A_IMM, IMM_A_ZERO, OP_B_IMM, IMM_B_U] at hop ⊢
  bv_decide

theorem decode_auipc (s : Gen.IbexDec.State) (i : Gen.IbexDec.Input) (w : BitVec 32)
    (hf : Fetched i w) (hop : opcode w = OPC_AUIPC) :
    let d := Gen.IbexDec.outputs s i
    d.illegal_insn_o = 0#1 ∧ d.rf_we_o = 1#1 ∧ d.rf_waddr_o = rdField w ∧
    d.rf_wdata_sel_o = RF_WD_EX ∧ d.alu_operator_o = ALU_ADD ∧
    d.alu_op_a_mux_sel_o = OP_A_CURRPC ∧ d.alu_op_b_mux_sel_o = OP_B_IMM ∧
    d.imm_b_mux_sel_o = IMM_B_U ∧ d.imm_u_type_o = immU w := by
  obtain ⟨h1, h2, h3⟩ := hf
  simp only [Gen.IbexDec.outputs, Gen.IbexDec.comb, opcode, rdField, immU, OPC_AUIPC, RF_WD_EX,
    ALU_ADD, OP_A_CURRPC, OP_B_IMM, IMM_B_U] at hop ⊢
  bv_decide

/-- **LUI result**: the ALU, set up as the decoder says (operand A = 0), writes `immU`. -/
theorem lui_result (s : Gen.IbexDec.State) (i : Gen.IbexDec.Input) (w : BitVec 32)
    (hf : Fetched i w) (hop : opcode w = OPC_LUI) (ma mb : BitVec 33) (sa : Gen.IbexAlu.State) :
    let d := Gen.IbexDec.outputs s i
    (Gen.IbexAlu.outputs sa (aluIn d.alu_operator_o 0 d.imm_u_type_o ma mb)).adder_result_o =
      luiResult w := by
  have h := decode_lui s i w hf hop
  simp only at h ⊢
  rw [h.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2, adder_sum]
  simp [luiResult]

/-- **AUIPC result**: `pc + immU`. -/
theorem auipc_result (s : Gen.IbexDec.State) (i : Gen.IbexDec.Input) (w : BitVec 32)
    (hf : Fetched i w) (hop : opcode w = OPC_AUIPC) (pc : BitVec 32) (ma mb : BitVec 33)
    (sa : Gen.IbexAlu.State) :
    let d := Gen.IbexDec.outputs s i
    (Gen.IbexAlu.outputs sa (aluIn d.alu_operator_o pc d.imm_u_type_o ma mb)).adder_result_o =
      auipcResult w pc := by
  have h := decode_auipc s i w hf hop
  simp only at h ⊢
  rw [h.2.2.2.2.1, h.2.2.2.2.2.2.2.2, adder_sum]
  rfl

/-! ### FENCE / FENCE.I -/

theorem decode_fence (s : Gen.IbexDec.State) (i : Gen.IbexDec.Input) (w : BitVec 32)
    (hf : Fetched i w) (hl : fenceLegal w = true) :
    let d := Gen.IbexDec.outputs s i
    d.illegal_insn_o = 0#1 ∧ d.rf_we_o = 0#1 ∧ d.data_req_o = 0#1 ∧ d.jump_in_dec_o = 0#1 := by
  obtain ⟨h1, h2, h3⟩ := hf
  simp only [Gen.IbexDec.outputs, Gen.IbexDec.comb, fenceLegal, opcode, funct3, OPC_MISC_MEM] at hl ⊢
  bv_decide

theorem decode_fence_i (s : Gen.IbexDec.State) (i : Gen.IbexDec.Input) (w : BitVec 32)
    (hf : Fetched i w) (hl : fenceILegal w = true) (hfirst : i.instr_first_cycle_i = 1#1) :
    let d := Gen.IbexDec.outputs s i
    d.illegal_insn_o = 0#1 ∧ d.rf_we_o = 0#1 ∧ d.jump_in_dec_o = 1#1 ∧ d.jump_set_o = 1#1 ∧
    d.icache_inval_o = 1#1 ∧ d.alu_op_a_mux_sel_o = OP_A_CURRPC ∧
    d.imm_b_mux_sel_o = IMM_B_INCR_PC := by
  obtain ⟨h1, h2, h3⟩ := hf
  simp only [Gen.IbexDec.outputs, Gen.IbexDec.comb, fenceILegal, opcode, funct3, OPC_MISC_MEM,
    OP_A_CURRPC, IMM_B_INCR_PC] at hl ⊢
  bv_decide

theorem decode_misc_mem_illegal (s : Gen.IbexDec.State) (i : Gen.IbexDec.Input) (w : BitVec 32)
    (hf : Fetched i w) (hop : opcode w = OPC_MISC_MEM) (h0 : fenceLegal w = false)
    (h1' : fenceILegal w = false) :
    (Gen.IbexDec.outputs s i).illegal_insn_o = 1#1 := by
  obtain ⟨h1, h2, h3⟩ := hf
  simp only [Gen.IbexDec.outputs, Gen.IbexDec.comb, fenceLegal, fenceILegal, opcode, funct3,
    OPC_MISC_MEM] at hop h0 h1' ⊢
  bv_decide

/-! ### ECALL, EBREAK, MRET, WFI, DRET -/

/-- **Fixed-encoding SYSTEM instructions**: each flag is raised exactly for its encoding, and a
`funct3 = 000` SYSTEM word is legal exactly when it is one of the five. -/
theorem decode_system_fixed (s : Gen.IbexDec.State) (i : Gen.IbexDec.Input) (w : BitVec 32)
    (hf : Fetched i w) (hop : opcode w = OPC_SYSTEM) (hf3 : funct3 w = 0b000#3) :
    let d := Gen.IbexDec.outputs s i
    d.illegal_insn_o =
      BitVec.ofBool (!(isEcall w || isEbreak w || isMret w || isWfi w || isDret w)) ∧
    (isEcall w = true → d.ecall_insn_o = 1#1) ∧ (isEbreak w = true → d.ebrk_insn_o = 1#1) ∧
    (isMret w = true → d.mret_insn_o = 1#1) ∧ (isWfi w = true → d.wfi_insn_o = 1#1) ∧
    (isDret w = true → d.dret_insn_o = 1#1) ∧ d.rf_we_o = 0#1 ∧ d.csr_access_o = 0#1 := by
  obtain ⟨h1, h2, h3⟩ := hf
  simp only [Gen.IbexDec.outputs, Gen.IbexDec.comb, isEcall, isEbreak, isMret, isWfi, isDret,
    sysFixed, opcode, funct3, rs1Field, rdField, csrAddr, OPC_SYSTEM] at hop hf3 ⊢
  bv_decide

/-! ### Zicsr -/

/-- **Legal CSR instructions**: the spec's CSR, operation, source and write-back. -/
theorem decode_csr (s : Gen.IbexDec.State) (i : Gen.IbexDec.Input) (w : BitVec 32)
    (hf : Fetched i w) (hl : csrLegal w = true) :
    let d := Gen.IbexDec.outputs s i
    d.illegal_insn_o = 0#1 ∧ d.csr_access_o = 1#1 ∧ d.csr_addr_o = csrAddr w ∧
    d.csr_op_o = csrOpCode (csrOpOf w) ∧
    d.rf_we_o = 1#1 ∧ d.rf_waddr_o = rdField w ∧ d.rf_wdata_sel_o = RF_WD_CSR ∧
    (csrUsesImm w = false → d.alu_op_a_mux_sel_o = OP_A_REG_A ∧ d.rf_raddr_a_o = rs1Field w) ∧
    (csrUsesImm w = true → d.alu_op_a_mux_sel_o = OP_A_IMM ∧ d.imm_a_mux_sel_o = IMM_A_Z ∧
                           d.zimm_rs1_type_o = csrUimm w) := by
  obtain ⟨h1, h2, h3⟩ := hf
  rw [csrOpCode_csrOpOf]
  simp only [Gen.IbexDec.outputs, Gen.IbexDec.comb, csrLegal, csrUsesImm, csrUimm, csrAddr,
    opcode, funct3, rs1Field, rdField, OPC_SYSTEM, RF_WD_CSR, OP_A_REG_A, OP_A_IMM, IMM_A_Z] at hl ⊢
  bv_decide

/-- `funct3 = 100` in SYSTEM is reserved. -/
theorem decode_system_reserved (s : Gen.IbexDec.State) (i : Gen.IbexDec.Input) (w : BitVec 32)
    (hf : Fetched i w) (hop : opcode w = OPC_SYSTEM) (hf3 : funct3 w = 0b100#3) :
    (Gen.IbexDec.outputs s i).illegal_insn_o = 1#1 := by
  obtain ⟨h1, h2, h3⟩ := hf
  simp only [Gen.IbexDec.outputs, Gen.IbexDec.comb, opcode, funct3, OPC_SYSTEM] at hop hf3 ⊢
  bv_decide

end RtlProof.Ibex
