import RtlProof.Generated.IbexCDec
import RtlProof.RV32I.Compressed
import Std.Tactic.BVDecide

/-!
# Ibex compressed decoder vs. the RV32C spec (capstone Track 2)

`Gen.IbexCDec` is generated from lowRISC Ibex's `rtl/ibex_compressed_decoder.sv`
with `RV32ZC = RV32Zca` (standard C only) and `BaseIsa = BaseIsaRV32I`.

For **every** 32-bit fetch word whose low two bits are not `11` (a compressed
instruction), with every other input arbitrary, including the `undef_k`
fields that stand for the RTL's `x` defaults:

* `cdec_illegal`: Ibex raises `illegal_instr_o` exactly for encodings the spec
  calls illegal (reserved, RV64-only, F/D).
* `cdec_expand`: for every legal encoding, `instr_o` is the spec's 32-bit
  expansion, bit for bit.
* `cdec_passthrough`: a 32-bit instruction passes through unchanged and is not
  flagged.

Model-checking equivalent: an equivalence check between the decoder and a
reference model (a Jasper SEC or C2RTL-style check). Here the reference model
is written from the ISA manual, and the result is a theorem.
-/

namespace RtlProof.Ibex
open RV32I.C

/-- The 16-bit instruction in the fetch word. -/
def lo16 (i : Gen.IbexCDec.Input) : BitVec 16 := i.instr_i.setWidth 16

theorem cdec_illegal (s : Gen.IbexCDec.State) (i : Gen.IbexCDec.Input)
    (hc : i.instr_i.extractLsb 1 0 ≠ 3#2) :
    (Gen.IbexCDec.comb s i).illegal_instr_o = BitVec.ofBool (!cLegal (lo16 i)) := by
  simp only [Gen.IbexCDec.comb, lo16, cLegal, op, funct3, rd, rs2, imm6]
  bv_decide

theorem cdec_expand (s : Gen.IbexCDec.State) (i : Gen.IbexCDec.Input)
    (hc : i.instr_i.extractLsb 1 0 ≠ 3#2) (hl : cLegal (lo16 i) = true) :
    (Gen.IbexCDec.comb s i).instr_o = cExpand (lo16 i) := by
  simp only [Gen.IbexCDec.comb, lo16, cLegal, cExpand, op, funct3, rd, rs2, rdp, rs1p, imm6,
    x0, x1, x2, addi4spnImm, lwImm, jImm, addi16spImm, bImm, lwspImm, swspImm,
    iType, sType, bType, uType, jType, rType, OP_IMM, LOAD, STORE, LUI, JAL, JALR, BRANCH, OP] at hl ⊢
  bv_decide

theorem cdec_passthrough (s : Gen.IbexCDec.State) (i : Gen.IbexCDec.Input)
    (hc : i.instr_i.extractLsb 1 0 = 3#2) :
    (Gen.IbexCDec.comb s i).instr_o = i.instr_i ∧ (Gen.IbexCDec.comb s i).illegal_instr_o = 0#1 := by
  simp only [Gen.IbexCDec.comb]
  constructor <;> bv_decide

end RtlProof.Ibex
