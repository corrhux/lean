/-!
# RV32I specification (the parts the Ibex block proofs need)

Written from the RISC-V Unprivileged ISA manual, chapter "RV32I Base Integer
Instruction Set". This is the course's own readable spec, not the official
Sail model; docs/CAPSTONE_PRIMER.md §3 shows how the two line up.

* `AluOp.exec`: OP / OP-IMM semantics (ADD, SUB, SLL, SLT, SLTU, XOR, SRL,
  SRA, OR, AND). Shift amounts are the low 5 bits of the second operand.
* `BrOp.taken`: the six conditional-branch comparisons.
-/

namespace RV32I

/-- Integer register-register / register-immediate operations (RV32I §2.4). -/
inductive AluOp where
  | add | sub | sll | slt | sltu | xor | srl | sra | or | and
deriving DecidableEq, Repr

/-- What each operation computes on two 32-bit operands. -/
def AluOp.exec : AluOp → BitVec 32 → BitVec 32 → BitVec 32
  | .add,  a, b => a + b
  | .sub,  a, b => a - b
  | .sll,  a, b => a <<< b.setWidth 5               -- shift amount = low 5 bits
  | .slt,  a, b => (BitVec.ofBool (a.slt b)).setWidth 32
  | .sltu, a, b => (BitVec.ofBool (a.ult b)).setWidth 32
  | .xor,  a, b => a ^^^ b
  | .srl,  a, b => a >>> b.setWidth 5
  | .sra,  a, b => a.sshiftRight' (b.setWidth 5)
  | .or,   a, b => a ||| b
  | .and,  a, b => a &&& b

/-- Conditional branches (RV32I §2.5). -/
inductive BrOp where
  | beq | bne | blt | bge | bltu | bgeu
deriving DecidableEq, Repr

/-- Whether the branch is taken. -/
def BrOp.taken : BrOp → BitVec 32 → BitVec 32 → Bool
  | .beq,  a, b => a == b
  | .bne,  a, b => a != b
  | .blt,  a, b => a.slt b
  | .bge,  a, b => !(a.slt b)
  | .bltu, a, b => a.ult b
  | .bgeu, a, b => !(a.ult b)

end RV32I
