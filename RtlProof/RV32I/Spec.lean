/-!
# RV32I specification (the parts the Ibex block proofs need)

Written from the RISC-V Unprivileged ISA manual, chapter "RV32I Base Integer
Instruction Set". This is the course's own readable spec, not the official
Sail model; docs/CAPSTONE_PRIMER.md §3 shows how the two line up.

* `AluOp.exec`: OP / OP-IMM semantics (ADD, SUB, SLL, SLT, SLTU, XOR, SRL,
  SRA, OR, AND). Shift amounts are the low 5 bits of the second operand.
* `BrOp.taken`: the six conditional-branch comparisons.
* Decoding of OP, OP-IMM and BRANCH instructions: their fields, which
  encodings are legal, and which operation each one performs.
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

/-! ### Instruction fields and decoding (RV32I §2.2–2.5) -/

section Fields
variable (w : BitVec 32)

def opcode : BitVec 7 := w.extractLsb 6 0
def rdField : BitVec 5 := w.extractLsb 11 7
def funct3 : BitVec 3 := w.extractLsb 14 12
def rs1Field : BitVec 5 := w.extractLsb 19 15
def rs2Field : BitVec 5 := w.extractLsb 24 20
def funct7 : BitVec 7 := w.extractLsb 31 25
/-- The I-type immediate, sign-extended. -/
def immI : BitVec 32 := (w.extractLsb 31 20).signExtend 32

end Fields

def OPC_OP : BitVec 7 := 0x33#7
def OPC_OP_IMM : BitVec 7 := 0x13#7
def OPC_BRANCH : BitVec 7 := 0x63#7

/-- Legal register-register (OP) encodings: `funct7` is 0, or `0100000` for SUB and SRA. -/
def opLegal (w : BitVec 32) : Bool :=
  opcode w = OPC_OP &&
    (funct7 w = 0#7 || (funct7 w = 0x20#7 && (funct3 w = 0b000#3 || funct3 w = 0b101#3)))

/-- Legal register-immediate (OP-IMM) encodings: the shifts constrain `imm[11:5]`
(SLLI/SRLI need 0, SRAI needs `0100000`); the rest take any immediate. -/
def opImmLegal (w : BitVec 32) : Bool :=
  opcode w = OPC_OP_IMM &&
    (if funct3 w = 0b001#3 then funct7 w = 0#7
     else if funct3 w = 0b101#3 then funct7 w = 0#7 || funct7 w = 0x20#7
     else true)

/-- The operation an OP or OP-IMM instruction performs. -/
def aluOpOf (w : BitVec 32) : AluOp :=
  let f3 := funct3 w
  if f3 = 0b000#3 then (if opcode w = OPC_OP && funct7 w = 0x20#7 then .sub else .add)
  else if f3 = 0b001#3 then .sll
  else if f3 = 0b010#3 then .slt
  else if f3 = 0b011#3 then .sltu
  else if f3 = 0b100#3 then .xor
  else if f3 = 0b101#3 then (if funct7 w = 0x20#7 then .sra else .srl)
  else if f3 = 0b110#3 then .or
  else .and

/-- Legal branches: every `funct3` except `010` and `011`. -/
def branchLegal (w : BitVec 32) : Bool :=
  opcode w = OPC_BRANCH && funct3 w != 0b010#3 && funct3 w != 0b011#3

/-- The comparison a branch performs. -/
def brOpOf (w : BitVec 32) : BrOp :=
  let f3 := funct3 w
  if f3 = 0b000#3 then .beq else if f3 = 0b001#3 then .bne
  else if f3 = 0b100#3 then .blt else if f3 = 0b101#3 then .bge
  else if f3 = 0b110#3 then .bltu else .bgeu

end RV32I
