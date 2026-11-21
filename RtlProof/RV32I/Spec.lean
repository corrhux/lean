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
* Loads, stores and jumps: legal encodings, access size and signedness,
  effective addresses and jump targets.
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
/-- The S-type immediate (stores): `imm[11:5] = w[31:25]`, `imm[4:0] = w[11:7]`. -/
def immS : BitVec 32 := (w.extractLsb 31 25 ++ w.extractLsb 11 7 : BitVec 12).signExtend 32
/-- The B-type immediate (branches): `imm[12|10:5|4:1|11]`, bit 0 is zero. -/
def immB : BitVec 32 :=
  (w.extractLsb 31 31 ++ w.extractLsb 7 7 ++ w.extractLsb 30 25 ++ w.extractLsb 11 8 ++ 0#1
    : BitVec 13).signExtend 32
/-- The U-type immediate (LUI, AUIPC): `w[31:12]` followed by twelve zeros. -/
def immU : BitVec 32 := w.extractLsb 31 12 ++ 0#12
/-- The 12-bit CSR address of a Zicsr instruction. -/
def csrAddr : BitVec 12 := w.extractLsb 31 20
/-- The J-type immediate (JAL): `imm[20|10:1|11|19:12]`, bit 0 is zero. -/
def immJ : BitVec 32 :=
  (w.extractLsb 31 31 ++ w.extractLsb 19 12 ++ w.extractLsb 20 20 ++ w.extractLsb 30 21 ++ 0#1
    : BitVec 21).signExtend 32

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

/-! ### Loads, stores and jumps (RV32I §2.5–2.6) -/

def OPC_LOAD : BitVec 7 := 0x03#7
def OPC_STORE : BitVec 7 := 0x23#7
def OPC_JAL : BitVec 7 := 0x6f#7
def OPC_JALR : BitVec 7 := 0x67#7

/-- Access width in bytes. -/
inductive Size where
  | byte | half | word
deriving DecidableEq, Repr

/-- Legal loads: LB, LH, LW, LBU, LHU (`funct3` 000, 001, 010, 100, 101). -/
def loadLegal (w : BitVec 32) : Bool :=
  opcode w = OPC_LOAD &&
    (funct3 w = 0b000#3 || funct3 w = 0b001#3 || funct3 w = 0b010#3 ||
     funct3 w = 0b100#3 || funct3 w = 0b101#3)

/-- Legal stores: SB, SH, SW (`funct3` 000, 001, 010). -/
def storeLegal (w : BitVec 32) : Bool :=
  opcode w = OPC_STORE && (funct3 w = 0b000#3 || funct3 w = 0b001#3 || funct3 w = 0b010#3)

/-- Access size of a load or store: `funct3[1:0]`. -/
def accessSize (w : BitVec 32) : Size :=
  let s := (funct3 w).extractLsb 1 0
  if s = 0b00#2 then .byte else if s = 0b01#2 then .half else .word

/-- A load sign-extends its result unless it is LBU/LHU (`funct3[2] = 1`). -/
def loadSigned (w : BitVec 32) : Bool := (funct3 w).extractLsb 2 2 = 0#1

/-- Effective addresses: `rs1 + imm` (wrapping). -/
def loadAddr (w rs1v : BitVec 32) : BitVec 32 := rs1v + immI w
def storeAddr (w rs1v : BitVec 32) : BitVec 32 := rs1v + immS w

/-- JAL is always legal; JALR needs `funct3 = 000`. -/
def jalLegal (w : BitVec 32) : Bool := opcode w = OPC_JAL
def jalrLegal (w : BitVec 32) : Bool := opcode w = OPC_JALR && funct3 w = 0b000#3

/-- Jump targets. JALR clears bit 0 of `rs1 + imm`. -/
def jalTarget (w pc : BitVec 32) : BitVec 32 := pc + immJ w
def jalrTarget (w rs1v : BitVec 32) : BitVec 32 := (rs1v + immI w) &&& ~~~1#32
/-- Branch target when taken. -/
def branchTarget (w pc : BitVec 32) : BitVec 32 := pc + immB w

/-! ### LUI, AUIPC, FENCE, SYSTEM (RV32I §2.4, 2.7, 2.8; Zicsr; Zifencei; privileged spec) -/

def OPC_LUI : BitVec 7 := 0x37#7
def OPC_AUIPC : BitVec 7 := 0x17#7
def OPC_MISC_MEM : BitVec 7 := 0x0f#7
def OPC_SYSTEM : BitVec 7 := 0x73#7

/-- LUI writes `immU`; AUIPC writes `pc + immU`. -/
def luiResult (w : BitVec 32) : BitVec 32 := immU w
def auipcResult (w pc : BitVec 32) : BitVec 32 := pc + immU w

/-- FENCE (`funct3 = 000`) and FENCE.I (`funct3 = 001`, Zifencei) are the only MISC-MEM
instructions. -/
def fenceLegal (w : BitVec 32) : Bool := opcode w = OPC_MISC_MEM && funct3 w = 0b000#3
def fenceILegal (w : BitVec 32) : Bool := opcode w = OPC_MISC_MEM && funct3 w = 0b001#3

/-- `funct3 = 000` SYSTEM instructions are fully fixed encodings: rs1 = rd = 0 and a fixed
`imm[11:0]`. -/
def sysFixed (w : BitVec 32) (imm : BitVec 12) : Bool :=
  opcode w = OPC_SYSTEM && funct3 w = 0b000#3 && rs1Field w = 0#5 && rdField w = 0#5 &&
    csrAddr w = imm

def isEcall (w : BitVec 32) : Bool := sysFixed w 0x000#12
def isEbreak (w : BitVec 32) : Bool := sysFixed w 0x001#12
def isMret (w : BitVec 32) : Bool := sysFixed w 0x302#12   -- privileged spec
def isWfi (w : BitVec 32) : Bool := sysFixed w 0x105#12    -- privileged spec
def isDret (w : BitVec 32) : Bool := sysFixed w 0x7b2#12   -- debug spec

/-- Zicsr: CSRRW/S/C (`funct3` 001/010/011) and CSRRWI/SI/CI (101/110/111). -/
def csrLegal (w : BitVec 32) : Bool :=
  opcode w = OPC_SYSTEM && (funct3 w).extractLsb 1 0 != 0b00#2

/-- What a CSR instruction does to the CSR. CSRRS/CSRRC (and their immediate forms) whose
source operand field is zero only read: the spec says they must not write the CSR. -/
inductive CsrOp where
  | read | write | set | clear
deriving DecidableEq, Repr

def csrOpOf (w : BitVec 32) : CsrOp :=
  let k := (funct3 w).extractLsb 1 0
  if k = 0b01#2 then .write
  else if rs1Field w = 0#5 then .read
  else if k = 0b10#2 then .set
  else .clear

/-- The immediate forms take the 5-bit `uimm` in the rs1 field, zero-extended. -/
def csrUsesImm (w : BitVec 32) : Bool := (funct3 w).extractLsb 2 2 = 1#1
def csrUimm (w : BitVec 32) : BitVec 32 := (rs1Field w).setWidth 32

end RV32I
