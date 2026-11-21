import RtlProof.Generated.IbexAlu
import RtlProof.RV32I.Spec
import Std.Tactic.BVDecide

/-!
# Ibex ALU vs. the RV32I spec (capstone Track 2)

`Gen.IbexAlu` is generated from lowRISC Ibex's `rtl/ibex_alu.sv` (pinned in
`third_party/ibex`), converted with sv2v and translated by sv2lean, with
`RV32B = RV32BNone`, the "capstone" configuration in docs/CAPSTONE_IBEX.md.

For every RV32I ALU operation and every pair of operands, the ALU's `result_o`
equals the spec, and for every branch condition `comparison_result_o` says
whether the branch is taken. These are combinational facts, so each is one
`bv_decide` call per operation.

Assumption: `multdiv_sel_i = 0`. That input hands the adder to the
multiply/divide unit; the decoder only raises it for M-extension
instructions, never together with an RV32I ALU operation.

Things worth noticing in the RTL that the proofs cover:
* SUB, the comparisons and SLT share one 33-bit adder:
  `{a,1} + ({b,0} ^ 1…1)`, i.e. `a + ~b + 1`.
* Right shifts reuse the left shifter by bit-reversing the operand
  (`shift_left` when `operator_i` is SLL, otherwise reversed in and out).
-/

namespace RtlProof.Ibex
open RV32I

/-- Ibex's encoding of each RV32I ALU operation (`alu_op_e` in ibex_pkg.sv). -/
def aluOpCode : AluOp → BitVec 7
  | .add => 0 | .sub => 1 | .xor => 2 | .or => 3 | .and => 4
  | .sra => 8 | .srl => 9 | .sll => 10 | .slt => 40 | .sltu => 41

/-- Ibex's encoding of each branch comparison. -/
def brOpCode : BrOp → BitVec 7
  | .blt => 23 | .bltu => 24 | .bge => 25 | .bgeu => 26 | .beq => 27 | .bne => 28

/-- The ALU's inputs for operation code `code` on operands `a`, `b`. The multiply/divide
operands are arbitrary; they are ignored while `multdiv_sel_i = 0`. -/
def aluIn (code : BitVec 7) (a b : BitVec 32) (ma mb : BitVec 33) : Gen.IbexAlu.Input :=
  { operator_i := code, operand_a_i := a, operand_b_i := b,
    multdiv_operand_a_i := ma, multdiv_operand_b_i := mb, multdiv_sel_i := 0 }

/-- **Every RV32I ALU operation computes the spec result.** -/
theorem alu_result (op : AluOp) (a b : BitVec 32) (ma mb : BitVec 33) (s : Gen.IbexAlu.State) :
    (Gen.IbexAlu.comb s (aluIn (aluOpCode op) a b ma mb)).result_o = op.exec a b := by
  cases op <;> simp only [Gen.IbexAlu.comb, aluIn, aluOpCode, AluOp.exec] <;> bv_decide

/-- **Every branch comparison agrees with the spec.** -/
theorem alu_branch (op : BrOp) (a b : BitVec 32) (ma mb : BitVec 33) (s : Gen.IbexAlu.State) :
    (Gen.IbexAlu.comb s (aluIn (brOpCode op) a b ma mb)).comparison_result_o =
      BitVec.ofBool (op.taken a b) := by
  cases op <;> simp only [Gen.IbexAlu.comb, aluIn, brOpCode, BrOp.taken] <;> bv_decide

end RtlProof.Ibex
