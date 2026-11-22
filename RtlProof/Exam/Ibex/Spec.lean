import RtlProof.Generated.IbexLSU
import RtlProof.Generated.IbexMD
import RtlProof.Generated.IbexAlu

/-!
# Ibex exam: the vocabulary the statements are written in

**Do not edit.** The grader checks this file's hash: a statement means what it
means only together with these definitions.

Two Ibex blocks, generated unmodified from lowRISC Ibex by `capstone/ibex/generate.sh`:

* `Gen.IbexMD`: `ibex_multdiv_slow`, the iterative multiplier/divider. It borrows
  the ALU's adder (`alu_adder_*_i`) and keeps two intermediate values in the ID
  stage (`imd_val_*`).
* `Gen.IbexLSU`: `ibex_load_store_unit` with `BaseIsa = RV32I` (the CHERIoT paths
  are compiled out) and no memory ECC.

Registers with an asynchronous reset appear twice: the flop (`md_state_q_ff`) and
the value the RTL reads (`md_state_q` in `comb`), which is the reset value while
`rst_ni = 0`. Every statement assumes `rst_ni = 1` in the cycles it talks about.
-/

namespace IbexExam

/-! ## `ibex_multdiv_slow` -/

namespace MD
open Gen.IbexMD

/-! `md_fsm_e` -/
abbrev IDLE : BitVec 3 := 0
abbrev ABS_A : BitVec 3 := 1
abbrev ABS_B : BitVec 3 := 2
abbrev COMP : BitVec 3 := 3
abbrev LAST : BitVec 3 := 4
abbrev CHANGE_SIGN : BitVec 3 := 5
abbrev FINISH : BitVec 3 := 6

/-! `md_op_e` -/
abbrev MULL : BitVec 2 := 0
abbrev MULH : BitVec 2 := 1
abbrev DIV : BitVec 2 := 2
abbrev REM : BitVec 2 := 3

/-- The control state: FSM state and iteration counter. -/
def ctl (s : State) : BitVec 3 × BitVec 5 := (s.md_state_q_ff, s.multdiv_count_q_ff)

/-- The control inputs. Everything else (operands, ALU results, intermediate values,
`equal_to_zero_i`, `signed_mode_i`) is data. -/
def ctlIn (i : Input) :
    BitVec 1 × BitVec 1 × BitVec 1 × BitVec 1 × BitVec 1 × BitVec 2 × BitVec 1 × BitVec 1 :=
  (i.rst_ni, i.mult_en_i, i.div_en_i, i.mult_sel_i, i.div_sel_i, i.operator_i,
   i.data_ind_timing_i, i.multdiv_ready_id_i)

/-- One cycle of a multiply (`op` = MULL or MULH) as the ID stage drives it: out of
reset, the multiplier enabled and selected, data-independent timing on, and the
result taken as soon as it is valid. -/
def MulCycle (op : BitVec 2) (i : Input) : Prop :=
  i.rst_ni = 1#1 ∧ i.mult_en_i = 1#1 ∧ i.mult_sel_i = 1#1 ∧ i.div_en_i = 0#1 ∧
  i.div_sel_i = 0#1 ∧ i.operator_i = op ∧ i.data_ind_timing_i = 1#1 ∧ i.multdiv_ready_id_i = 1#1

/-- One cycle of a divide (`op` = DIV or REM), likewise. -/
def DivCycle (op : BitVec 2) (i : Input) : Prop :=
  i.rst_ni = 1#1 ∧ i.div_en_i = 1#1 ∧ i.div_sel_i = 1#1 ∧ i.mult_en_i = 0#1 ∧
  i.mult_sel_i = 0#1 ∧ i.operator_i = op ∧ i.data_ind_timing_i = 1#1 ∧ i.multdiv_ready_id_i = 1#1

/-- `valid_o`: the result is ready this cycle. -/
def valid (s : State) (i : Input) : BitVec 1 := (outputs s i).valid_o

/-! ### The multiplier connected to what it borrows (for the challenge)

`ibex_multdiv_slow` does not add by itself: it hands two operands to the ALU and reads
the sum back, and its running sum and numerator live in the ID stage's `imd_val_q`
registers. `System` is the three together; `sysStep` is one clock edge. -/

/-- The multiplier's registers plus the ID stage's two intermediate-value registers. -/
structure System where
  md : State
  imd0 : BitVec 34      -- `imd_val_q[0]`: the running sum (`accum_window_q`)
  imd1 : BitVec 34      -- `imd_val_q[1]`: the numerator, for divisions
deriving Repr

/-- The inputs for one cycle of `op a b`, given the intermediate values and the ALU's sum.
The `undef_*` inputs (the RTL's `x` values) are taken as 0. -/
def sysInput (op mode : BitVec 2) (a b : BitVec 32) (x : System)
    (sumExt : BitVec 34) (sum : BitVec 32) : Input :=
  { (default : Input) with
    rst_ni := 1#1, mult_en_i := 1#1, mult_sel_i := 1#1, operator_i := op, signed_mode_i := mode,
    op_a_i := a, op_b_i := b, data_ind_timing_i := 1#1, multdiv_ready_id_i := 1#1,
    imd_val_q_i := x.imd0 ++ x.imd1,          -- sv2v packs element 0 in the high bits
    alu_adder_ext_i := sumExt, alu_adder_i := sum }

/-- One clock edge of the multiplier, the ALU's adder and the `imd_val` registers. -/
def sysStep (op mode : BitVec 2) (a b : BitVec 32) (x : System) : System :=
  -- The operands the multiplier hands to the ALU do not depend on the sum it gets back.
  let o0 := outputs x.md (sysInput op mode a b x 0 0)
  let alu := Gen.IbexAlu.outputs default
    { operator_i := 0, operand_a_i := 0, operand_b_i := 0,
      multdiv_operand_a_i := o0.alu_operand_a_o, multdiv_operand_b_i := o0.alu_operand_b_o,
      multdiv_sel_i := 1#1 }
  let i := sysInput op mode a b x alu.adder_result_ext_o alu.adder_result_o
  let o := outputs x.md i
  { md := step x.md i,
    imd0 := if o.imd_val_we_o.getLsbD 0 then o.imd_val_d_o.extractLsb' 34 34 else x.imd0,
    imd1 := if o.imd_val_we_o.getLsbD 1 then o.imd_val_d_o.extractLsb' 0 34 else x.imd1 }

/-- The multiplier's result output in a given cycle of the system. -/
def sysResult (op mode : BitVec 2) (a b : BitVec 32) (x : System) : BitVec 32 :=
  let o0 := outputs x.md (sysInput op mode a b x 0 0)
  let alu := Gen.IbexAlu.outputs default
    { operator_i := 0, operand_a_i := 0, operand_b_i := 0,
      multdiv_operand_a_i := o0.alu_operand_a_o, multdiv_operand_b_i := o0.alu_operand_b_o,
      multdiv_sel_i := 1#1 }
  (outputs x.md (sysInput op mode a b x alu.adder_result_ext_o alu.adder_result_o)).multdiv_result_o

/-- The system after `n` cycles of `op a b`, from the multiplier's idle state. -/
def sysRun (op mode : BitVec 2) (a b : BitVec 32) (x0 : System) : Nat → System
  | 0 => x0
  | n + 1 => sysStep op mode a b (sysRun op mode a b x0 n)

end MD

/-! ## `ibex_load_store_unit` -/

namespace LSU
open Gen.IbexLSU

/-! `ls_fsm_e` (the CHERIoT states 5–7 are unreachable with `BaseIsa = RV32I`) -/
abbrev IDLE : BitVec 4 := 0
abbrev WAIT_GNT_MIS : BitVec 4 := 1
abbrev WAIT_RVALID_MIS : BitVec 4 := 2
abbrev WAIT_GNT : BitVec 4 := 3
abbrev WAIT_RVALID_MIS_GNTS_DONE : BitVec 4 := 4

/-- Out of reset. -/
def Live (i : Input) : Prop := i.rst_ni = 1#1

/-- The byte offset of an address within its word. -/
def off (a : BitVec 32) : BitVec 2 := a.setWidth 2

/-- The word address the bus sees. -/
def wordAddr (a : BitVec 32) : BitVec 32 := a &&& ~~~3#32

/-- A byte offset as a shift amount in bits. -/
def bits (o : BitVec 2) : BitVec 32 := o.setWidth 32 * 8#32

/-- The bytes an access touches, as a mask on the low bytes.
`lsu_type`: `00` word, `01` halfword, `1x` byte. -/
def sizeMask (t : BitVec 2) : BitVec 32 :=
  if t = 0#2 then 0xFFFFFFFF#32 else if t = 1#2 then 0x0000FFFF#32 else 0x000000FF#32

/-- An access fits in one word: a word must be aligned, a halfword must not start in the
last byte. (Ibex splits the others into two bus transactions.) -/
def Fits (a : BitVec 32) (t : BitVec 2) : Prop :=
  (t = 0#2 → off a = 0#2) ∧ (t = 1#2 → off a ≠ 3#2)

/-- The bus's byte enables as a bit mask. -/
def byteMask (be : BitVec 4) : BitVec 32 :=
  (bif be.getLsbD 3 then 0xFF000000#32 else 0#32) ||| (bif be.getLsbD 2 then 0x00FF0000#32 else 0#32) |||
  (bif be.getLsbD 1 then 0x0000FF00#32 else 0#32) ||| (bif be.getLsbD 0 then 0x000000FF#32 else 0#32)

/-- What a bus write does to the addressed memory word: the enabled bytes take the write
data, the others keep their value. -/
def busWrite (old : BitVec 32) (be : BitVec 4) (wdata : BitVec 32) : BitVec 32 :=
  (old &&& ~~~(byteMask be)) ||| (wdata &&& byteMask be)

/-- The ISA's store (SB, SH, SW) to an access that fits in the word: the low bytes of `v`
replace the bytes at the address. -/
def storeSpec (old : BitVec 32) (a : BitVec 32) (t : BitVec 2) (v : BitVec 32) : BitVec 32 :=
  let m := sizeMask t <<< bits (off a)
  (old &&& ~~~m) ||| ((v <<< bits (off a)) &&& m)

/-- The ISA's load (LB, LBU, LH, LHU, LW) from an access that fits in the word: the bytes
at the address, sign-extended if `sext = 1` and zero-extended otherwise. -/
def loadSpec (w : BitVec 32) (a : BitVec 32) (t : BitVec 2) (sext : BitVec 1) : BitVec 32 :=
  let x := w >>> bits (off a)
  if t = 0#2 then x
  else if t = 1#2 then (if sext = 1#1 then (x.setWidth 16).signExtend 32 else (x.setWidth 16).setWidth 32)
  else (if sext = 1#1 then (x.setWidth 8).signExtend 32 else (x.setWidth 8).setWidth 32)

/-- The ISA's word load from a misaligned address: the four bytes starting at the offset,
from the word at the address (`w0`) and the next one (`w1`). -/
def loadWordSpan (w0 w1 : BitVec 32) (a : BitVec 32) : BitVec 32 :=
  ((w1 ++ w0) >>> ((off a).setWidth 64 * 8#64)).setWidth 32

end LSU

end IbexExam
