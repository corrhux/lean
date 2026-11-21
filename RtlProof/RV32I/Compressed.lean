import RtlProof.RV32I.Spec

/-!
# RV32C: legality and expansion of 16-bit instructions

From the RISC-V Unprivileged ISA, chapter "C" Extension for Compressed
Instructions (Zca, RV32, no F/D). Every legal 16-bit instruction expands to
exactly one 32-bit RV32I instruction (Table "RVC opcode map").

* `cLegal c`: `c` is a defined RV32C instruction. HINTs (e.g. `C.NOP`, a
  `C.ADDI`/`C.LI`/`C.LUI`/`C.MV`/`C.ADD`/`C.SLLI` with `rd = x0`, or a zero
  shift amount) are legal. RESERVED encodings, RV64-only and F/D
  instructions are not.
* `cExpand c`: the 32-bit instruction it stands for (meaningful only when legal).

Register fields: `rd'`/`rs1'`/`rs2'` are 3-bit fields naming x8–x15.
-/

namespace RV32I.C

/-! ### Base-ISA encoders -/

def OP_IMM : BitVec 7 := 0b0010011#7
def LOAD   : BitVec 7 := 0b0000011#7
def STORE  : BitVec 7 := 0b0100011#7
def LUI    : BitVec 7 := 0b0110111#7
def JAL    : BitVec 7 := 0b1101111#7
def JALR   : BitVec 7 := 0b1100111#7
def BRANCH : BitVec 7 := 0b1100011#7
def OP     : BitVec 7 := 0b0110011#7

def iType (imm : BitVec 12) (rs1 : BitVec 5) (f3 : BitVec 3) (rd : BitVec 5) (opc : BitVec 7) :
    BitVec 32 := imm ++ rs1 ++ f3 ++ rd ++ opc

def sType (imm : BitVec 12) (rs2 rs1 : BitVec 5) (f3 : BitVec 3) (opc : BitVec 7) : BitVec 32 :=
  imm.extractLsb 11 5 ++ rs2 ++ rs1 ++ f3 ++ imm.extractLsb 4 0 ++ opc

def bType (imm : BitVec 13) (rs2 rs1 : BitVec 5) (f3 : BitVec 3) : BitVec 32 :=
  imm.extractLsb 12 12 ++ imm.extractLsb 10 5 ++ rs2 ++ rs1 ++ f3 ++ imm.extractLsb 4 1 ++
    imm.extractLsb 11 11 ++ BRANCH

def uType (imm : BitVec 20) (rd : BitVec 5) (opc : BitVec 7) : BitVec 32 := imm ++ rd ++ opc

def jType (imm : BitVec 21) (rd : BitVec 5) : BitVec 32 :=
  imm.extractLsb 20 20 ++ imm.extractLsb 10 1 ++ imm.extractLsb 11 11 ++ imm.extractLsb 19 12 ++
    rd ++ JAL

def rType (f7 : BitVec 7) (rs2 rs1 : BitVec 5) (f3 : BitVec 3) (rd : BitVec 5) (opc : BitVec 7) :
    BitVec 32 := f7 ++ rs2 ++ rs1 ++ f3 ++ rd ++ opc

/-! ### Fields of a 16-bit instruction -/

section
variable (c : BitVec 16)

def op : BitVec 2 := c.extractLsb 1 0
def funct3 : BitVec 3 := c.extractLsb 15 13
def rd : BitVec 5 := c.extractLsb 11 7          -- also rs1 in CR/CI formats
def rs2 : BitVec 5 := c.extractLsb 6 2
def rdp : BitVec 5 := 0b01#2 ++ c.extractLsb 4 2   -- rd'  / rs2' (bits 4:2)
def rs1p : BitVec 5 := 0b01#2 ++ c.extractLsb 9 7  -- rs1' / rd'  (bits 9:7)
def imm6 : BitVec 6 := c.extractLsb 12 12 ++ c.extractLsb 6 2   -- CI immediate

def x0 : BitVec 5 := 0#5
def x1 : BitVec 5 := 1#5
def x2 : BitVec 5 := 2#5

/-- C.ADDI4SPN: nzuimm[5:4|9:6|2|3] in bits 12:5. -/
def addi4spnImm : BitVec 12 :=
  0b00#2 ++ c.extractLsb 10 7 ++ c.extractLsb 12 11 ++ c.extractLsb 5 5 ++ c.extractLsb 6 6 ++ 0b00#2
/-- C.LW / C.SW: uimm[5:3] in 12:10, uimm[2|6] in 6:5. -/
def lwImm : BitVec 12 :=
  0#5 ++ c.extractLsb 5 5 ++ c.extractLsb 12 10 ++ c.extractLsb 6 6 ++ 0b00#2
/-- C.JAL / C.J: offset[11|4|9:8|10|6|7|3:1|5] in bits 12:2. -/
def jImm : BitVec 21 :=
  (c.extractLsb 12 12 ++ c.extractLsb 8 8 ++ c.extractLsb 10 9 ++ c.extractLsb 6 6 ++
    c.extractLsb 7 7 ++ c.extractLsb 2 2 ++ c.extractLsb 11 11 ++ c.extractLsb 5 3 ++ 0#1
    : BitVec 12).signExtend 21
/-- C.ADDI16SP: nzimm[9|4|6|8:7|5] in bits 12, 6:2. -/
def addi16spImm : BitVec 12 :=
  (c.extractLsb 12 12 ++ c.extractLsb 4 3 ++ c.extractLsb 5 5 ++ c.extractLsb 2 2 ++
    c.extractLsb 6 6 ++ 0#4 : BitVec 10).signExtend 12
/-- C.BEQZ / C.BNEZ: offset[8|4:3] in 12:10, offset[7:6|2:1|5] in 6:2. -/
def bImm : BitVec 13 :=
  (c.extractLsb 12 12 ++ c.extractLsb 6 5 ++ c.extractLsb 2 2 ++ c.extractLsb 11 10 ++
    c.extractLsb 4 3 ++ 0#1 : BitVec 9).signExtend 13
/-- C.LWSP: uimm[5] in 12, uimm[4:2|7:6] in 6:2. -/
def lwspImm : BitVec 12 :=
  0#4 ++ c.extractLsb 3 2 ++ c.extractLsb 12 12 ++ c.extractLsb 6 4 ++ 0b00#2
/-- C.SWSP: uimm[5:2|7:6] in 12:7. -/
def swspImm : BitVec 12 := 0#4 ++ c.extractLsb 8 7 ++ c.extractLsb 12 9 ++ 0b00#2

end

/-! ### Legality -/

/-- Is `c` (with `c[1:0] ≠ 11`) a defined RV32C (Zca) instruction? -/
def cLegal (c : BitVec 16) : Bool :=
  let f3 := funct3 c
  if op c = 0b00#2 then
    (f3 = 0b000#3 && c.extractLsb 12 5 != 0#8)        -- C.ADDI4SPN (nzuimm = 0 is reserved)
      || f3 = 0b010#3 || f3 = 0b110#3                 -- C.LW, C.SW (C.FLD/FLW/FSD/FSW: no F/D)
  else if op c = 0b01#2 then
    if f3 = 0b011#3 then imm6 c != 0#6                -- C.ADDI16SP / C.LUI: zero immediate reserved
    else if f3 = 0b100#3 then
      let f2 := c.extractLsb 11 10
      if f2 = 0b10#2 then true                        -- C.ANDI
      else if f2 = 0b11#2 then c.extractLsb 12 12 = 0#1   -- C.SUB/XOR/OR/AND; bit 12 = 1 is RV64/reserved
      else c.extractLsb 12 12 = 0#1                   -- C.SRLI/C.SRAI: shamt[5] must be 0 on RV32
    else true                                         -- C.ADDI, C.JAL, C.LI, C.J, C.BEQZ, C.BNEZ
  else if op c = 0b10#2 then
    if f3 = 0b000#3 then c.extractLsb 12 12 = 0#1     -- C.SLLI: shamt[5] must be 0 on RV32
    else if f3 = 0b010#3 then rd c != 0#5             -- C.LWSP: rd = x0 reserved
    else if f3 = 0b100#3 then
      !(c.extractLsb 12 12 = 0#1 && rs2 c = 0#5 && rd c = 0#5)   -- C.JR with rs1 = x0 reserved
    else f3 = 0b110#3                                 -- C.SWSP (C.FLDSP/FLWSP/FSDSP/FSWSP: no F/D)
  else false

/-! ### Expansion -/

/-- The 32-bit instruction a legal 16-bit instruction stands for. -/
def cExpand (c : BitVec 16) : BitVec 32 :=
  let f3 := funct3 c
  if op c = 0b00#2 then
    if f3 = 0b000#3 then iType (addi4spnImm c) x2 0b000#3 (rdp c) OP_IMM         -- C.ADDI4SPN
    else if f3 = 0b010#3 then iType (lwImm c) (rs1p c) 0b010#3 (rdp c) LOAD       -- C.LW
    else sType (lwImm c) (rdp c) (rs1p c) 0b010#3 STORE                           -- C.SW
  else if op c = 0b01#2 then
    if f3 = 0b000#3 then iType ((imm6 c).signExtend 12) (rd c) 0b000#3 (rd c) OP_IMM   -- C.ADDI
    else if f3 = 0b001#3 then jType (jImm c) x1                                        -- C.JAL
    else if f3 = 0b010#3 then iType ((imm6 c).signExtend 12) x0 0b000#3 (rd c) OP_IMM  -- C.LI
    else if f3 = 0b011#3 then
      if rd c = x2 then iType (addi16spImm c) x2 0b000#3 x2 OP_IMM                    -- C.ADDI16SP
      else uType ((imm6 c).signExtend 20) (rd c) LUI                                   -- C.LUI
    else if f3 = 0b100#3 then
      let f2 := c.extractLsb 11 10
      if f2 = 0b00#2 then iType (0#7 ++ c.extractLsb 6 2) (rs1p c) 0b101#3 (rs1p c) OP_IMM       -- C.SRLI
      else if f2 = 0b01#2 then
        iType (0b0100000#7 ++ c.extractLsb 6 2) (rs1p c) 0b101#3 (rs1p c) OP_IMM                 -- C.SRAI
      else if f2 = 0b10#2 then iType ((imm6 c).signExtend 12) (rs1p c) 0b111#3 (rs1p c) OP_IMM  -- C.ANDI
      else
        let f := c.extractLsb 6 5
        if f = 0b00#2 then rType 0b0100000#7 (rdp c) (rs1p c) 0b000#3 (rs1p c) OP              -- C.SUB
        else if f = 0b01#2 then rType 0#7 (rdp c) (rs1p c) 0b100#3 (rs1p c) OP                 -- C.XOR
        else if f = 0b10#2 then rType 0#7 (rdp c) (rs1p c) 0b110#3 (rs1p c) OP                 -- C.OR
        else rType 0#7 (rdp c) (rs1p c) 0b111#3 (rs1p c) OP                                     -- C.AND
    else if f3 = 0b101#3 then jType (jImm c) x0                                         -- C.J
    else if f3 = 0b110#3 then bType (bImm c) x0 (rs1p c) 0b000#3                         -- C.BEQZ
    else bType (bImm c) x0 (rs1p c) 0b001#3                                             -- C.BNEZ
  else
    if f3 = 0b000#3 then iType (0#7 ++ c.extractLsb 6 2) (rd c) 0b001#3 (rd c) OP_IMM    -- C.SLLI
    else if f3 = 0b010#3 then iType (lwspImm c) x2 0b010#3 (rd c) LOAD                   -- C.LWSP
    else if f3 = 0b100#3 then
      if c.extractLsb 12 12 = 0#1 then
        if rs2 c = 0#5 then iType 0#12 (rd c) 0b000#3 x0 JALR                            -- C.JR
        else rType 0#7 (rs2 c) x0 0b000#3 (rd c) OP                                      -- C.MV
      else if rs2 c = 0#5 && rd c = 0#5 then 0x00100073#32                              -- C.EBREAK
      else if rs2 c = 0#5 then iType 0#12 (rd c) 0b000#3 x1 JALR                         -- C.JALR
      else rType 0#7 (rs2 c) (rd c) 0b000#3 (rd c) OP                                    -- C.ADD
    else sType (swspImm c) (rs2 c) x2 0b010#3 STORE                                      -- C.SWSP

end RV32I.C
