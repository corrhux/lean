import RtlProof.Generated.IbexRF
import Std.Tactic.BVDecide

/-!
# Ibex register file vs. the ISA's view of `x0 … x31`

`Gen.IbexRF` is generated from `rtl/ibex_register_file_ff.sv` with
`BaseIsa = RV32I`, `RV32E = 0`, `DummyInstructions = 0`: 31 flip-flop
registers for x1–x31, x0 hard-wired.

The ISA treats the register file as a memory: x0 always reads 0, and a write
to `rd ≠ x0` changes exactly that register. The theorems say this about the
RTL **for every state of all 31 registers, every read and write address,
value and enable**, for both read ports, and for the `x` read defaults
(`undef_k`) as well. Each is a sequential fact over one clock edge
(`step`), discharged by `bv_decide` over all 992 register bits at once.

Side inputs fixed for the plain-RV32I core: dummy instructions are off
(`dummy_instr_*_i = 0`). `test_en_i` and `cheriot_enable_i` are arbitrary.

The read claims assume the read cycle is not in reset: Ibex's reset is
asynchronous, so while `rst_ni = 0` every register already reads 0. `bv_decide`
found this when the hypothesis was missing; the counterexample read during
reset.
-/

namespace RtlProof.Ibex
open Gen.IbexRF

/-- Read port A of state `s` at address `a` (all other inputs as in `i`). -/
def readA (s : State) (i : Input) (a : BitVec 5) : BitVec 32 :=
  (outputs s { i with raddr_a_i := a }).rdata_a_o

def readB (s : State) (i : Input) (a : BitVec 5) : BitVec 32 :=
  (outputs s { i with raddr_b_i := a }).rdata_b_o

/-- The side inputs a plain-RV32I Ibex drives. -/
structure Plain (i : Input) : Prop where
  no_dummy_id : i.dummy_instr_id_i = 0#1
  no_dummy_wb : i.dummy_instr_wb_i = 0#1

/-- **x0 reads as zero**, on both ports, in every state. -/
theorem rf_x0 (s : State) (i : Input) (h : Plain i) :
    readA s i 0#5 = 0#32 ∧ readB s i 0#5 = 0#32 := by
  obtain ⟨h1, h2⟩ := h
  simp only [readA, readB, outputs, comb] at *
  bv_decide

/-- **A write to `rd ≠ x0` is seen by the next read of `rd`, and nothing else changes.**
`i` is the cycle with the write, `j` the inputs on the next cycle's read. -/
theorem rf_write (s : State) (i j : Input) (hi : Plain i) (hj : Plain j)
    (hrst : i.rst_ni = 1#1) (hjr : j.rst_ni = 1#1) (hwe : i.we_a_i = 1#1) (a : BitVec 5) :
    readA (step s i) j a =
      (if a = i.waddr_a_i ∧ a ≠ 0#5 then i.wdata_a_i else readA s j a) := by
  obtain ⟨h1, h2⟩ := hi
  obtain ⟨h3, h4⟩ := hj
  simp only [readA, outputs, comb, step] at *
  bv_decide

theorem rf_write_b (s : State) (i j : Input) (hi : Plain i) (hj : Plain j)
    (hrst : i.rst_ni = 1#1) (hjr : j.rst_ni = 1#1) (hwe : i.we_a_i = 1#1) (a : BitVec 5) :
    readB (step s i) j a =
      (if a = i.waddr_a_i ∧ a ≠ 0#5 then i.wdata_a_i else readB s j a) := by
  obtain ⟨h1, h2⟩ := hi
  obtain ⟨h3, h4⟩ := hj
  simp only [readB, outputs, comb, step] at *
  bv_decide

/-- **No write enable, no change.** -/
theorem rf_hold (s : State) (i j : Input) (hi : Plain i) (hj : Plain j)
    (hrst : i.rst_ni = 1#1) (hjr : j.rst_ni = 1#1) (hwe : i.we_a_i = 0#1) (a : BitVec 5) :
    readA (step s i) j a = readA s j a := by
  obtain ⟨h1, h2⟩ := hi
  obtain ⟨h3, h4⟩ := hj
  simp only [readA, outputs, comb, step] at *
  bv_decide

/-- **Reset clears every register** (`WordZeroVal = 0`). -/
theorem rf_reset (s : State) (i j : Input) (hi : Plain i) (hj : Plain j)
    (hrst : i.rst_ni = 0#1) (a : BitVec 5) :
    readA (step s i) j a = 0#32 := by
  obtain ⟨h1, h2⟩ := hi
  obtain ⟨h3, h4⟩ := hj
  simp only [readA, outputs, comb, step] at *
  bv_decide

end RtlProof.Ibex
