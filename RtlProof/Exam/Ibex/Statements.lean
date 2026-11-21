import RtlProof.Exam.Ibex.Spec
import RtlProof.Core.Circuit

/-!
# Ibex exam: the statements

**Do not edit.** Your exam files (`MultDiv.lean`, `LoadStore.lean`) repeat each
statement; the grader checks `example : Stmt.X := X`, so a changed statement fails.

Each `def` is a `Prop`: what you have to prove. Points are in brackets.
-/

namespace IbexExam.Stmt
open Gen

/-! ## Multiply/divide (`ibex_multdiv_slow`) -/

/-- **M1** [10] Ibex's own assertion `IbexMultDivStateValid`: the FSM is always in one of
its seven states. (Jasper: prove an SVA; here, from the reset state, for every input
sequence.) -/
def md_state_valid : Prop :=
  (IbexMD.circuit IbexMD.init0).Safe (fun s => s.md_state_q_ff ≤ 6#3)

/-- **M2** [15] Multiply latency: started from idle and run as the ID stage runs it,
`valid_o` is low for 32 cycles and high in cycle 32. -/
def mul_latency : Prop :=
  ∀ (op : BitVec 2), (op = MD.MULL ∨ op = MD.MULH) →
  ∀ (s0 : IbexMD.State), s0.md_state_q_ff = MD.IDLE →
  ∀ (ins : Nat → IbexMD.Input), (∀ n, MD.MulCycle op (ins n)) →
    (∀ k, k < 32 → MD.valid ((IbexMD.circuit s0).run ins k) (ins k) = 0#1) ∧
    MD.valid ((IbexMD.circuit s0).run ins 32) (ins 32) = 1#1

/-- **M3** [10] Divide latency: likewise, `valid_o` first rises in cycle 36. -/
def div_latency : Prop :=
  ∀ (op : BitVec 2), (op = MD.DIV ∨ op = MD.REM) →
  ∀ (s0 : IbexMD.State), s0.md_state_q_ff = MD.IDLE →
  ∀ (ins : Nat → IbexMD.Input), (∀ n, MD.DivCycle op (ins n)) →
    (∀ k, k < 36 → MD.valid ((IbexMD.circuit s0).run ins k) (ins k) = 0#1) ∧
    MD.valid ((IbexMD.circuit s0).run ins 36) (ins 36) = 1#1

/-- **M4** [20] Data-independent timing (Ibex's countermeasure `SEC_CM:
CORE.DATA_REG_SW.SCA`): with `data_ind_timing_i` set, two runs that see the same control
inputs keep the same control state and raise `valid_o` in the same cycles, whatever the
operands and whatever the ALU returns. (Jasper: a non-interference check on two copies of
the design.) -/
def constant_time : Prop :=
  ∀ (s t : IbexMD.State), MD.ctl s = MD.ctl t →
  ∀ (ins jns : Nat → IbexMD.Input),
    (∀ n, MD.ctlIn (ins n) = MD.ctlIn (jns n)) → (∀ n, (ins n).data_ind_timing_i = 1#1) →
    ∀ n, MD.ctl ((IbexMD.circuit s).run ins n) = MD.ctl ((IbexMD.circuit t).run jns n) ∧
         MD.valid ((IbexMD.circuit s).run ins n) (ins n) =
           MD.valid ((IbexMD.circuit t).run jns n) (jns n)

/-! ## Load/store unit (`ibex_load_store_unit`) -/

/-- **L1** [5] A bus request is held until it is granted: while waiting for a grant the
LSU drives `data_req_o`, and without a grant (and no PMP error) it keeps waiting. -/
def lsu_req_held : Prop :=
  ∀ (s : IbexLSU.State) (i : IbexLSU.Input), LSU.Live i →
    (s.ls_fsm_cs_ff = LSU.WAIT_GNT ∨ s.ls_fsm_cs_ff = LSU.WAIT_GNT_MIS) →
    (IbexLSU.outputs s i).data_req_o = 1#1 ∧
    (i.data_gnt_i = 0#1 → s.pmp_err_q_ff = 0#1 → (IbexLSU.step s i).ls_fsm_cs_ff = s.ls_fsm_cs_ff)

/-- **L2** [15] Stores do what the ISA says, in every reachable state: when a store that
fits in its word is issued, the bus request writes exactly the bytes SB/SH/SW write. -/
def lsu_store : Prop :=
  ∀ (ins : Nat → IbexLSU.Input), (∀ n, LSU.Live (ins n)) → ∀ n,
    let s := (IbexLSU.circuit IbexLSU.init0).run ins n
    let i := ins n
    s.ls_fsm_cs_ff = LSU.IDLE → i.lsu_req_i = 1#1 → i.lsu_we_i = 1#1 →
    LSU.Fits i.adder_result_ex_i i.lsu_type_i →
    let o := IbexLSU.outputs s i
    o.data_req_o = 1#1 ∧ o.data_we_o = 1#1 ∧ o.data_addr_o = LSU.wordAddr i.adder_result_ex_i ∧
    ∀ old, LSU.busWrite old o.data_be_o o.data_wdata_o =
      LSU.storeSpec old i.adder_result_ex_i i.lsu_type_i i.lsu_wdata_i

/-- **L3** [15] Loads return what the ISA says, however long memory takes: a load that
fits in its word is granted in cycle 0, memory answers in cycle `k + 1` after `k` idle
cycles, and the LSU hands back the ISA's value. -/
def lsu_load : Prop :=
  ∀ (s : IbexLSU.State) (ins : Nat → IbexLSU.Input) (k : Nat),
    s.ls_fsm_cs_ff = LSU.IDLE → (∀ n, LSU.Live (ins n)) →
    -- cycle 0: the request, granted at once, no PMP error
    (ins 0).lsu_req_i = 1#1 → (ins 0).lsu_we_i = 0#1 → (ins 0).data_gnt_i = 1#1 →
    (ins 0).data_pmp_err_i = 0#1 → LSU.Fits (ins 0).adder_result_ex_i (ins 0).lsu_type_i →
    -- cycles 1..k: no new request, no answer yet
    (∀ j, 1 ≤ j → j ≤ k → (ins j).lsu_req_i = 0#1 ∧ (ins j).data_rvalid_i = 0#1) →
    -- cycle k+1: memory answers without error
    (ins (k + 1)).data_rvalid_i = 1#1 → (ins (k + 1)).data_bus_err_i = 0#1 →
    let o := IbexLSU.outputs ((IbexLSU.circuit s).run ins (k + 1)) (ins (k + 1))
    o.lsu_rdata_valid_o = 1#1 ∧
    o.lsu_rdata_o = LSU.loadSpec (ins (k + 1)).data_rdata_i (ins 0).adder_result_ex_i
                      (ins 0).lsu_type_i (ins 0).lsu_sign_ext_i

/-- **L4** [10] A misaligned word load (LW at an address that is not a multiple of 4) is
split into two bus transactions, and the result is still the ISA's: the four bytes from
the address on, across the two words. In cycle 1 the LSU asks the core for the next
word's address (`addr_incr_req_o`) and requests it. -/
def lsu_load_misaligned : Prop :=
  ∀ (s : IbexLSU.State) (ins : Nat → IbexLSU.Input) (a : BitVec 32),
    s.ls_fsm_cs_ff = LSU.IDLE → (∀ n, LSU.Live (ins n)) → LSU.off a ≠ 0#2 →
    -- cycle 0: LW at `a`, granted at once, no PMP error
    (ins 0).lsu_req_i = 1#1 → (ins 0).lsu_we_i = 0#1 → (ins 0).lsu_type_i = 0#2 →
    (ins 0).adder_result_ex_i = a → (ins 0).data_gnt_i = 1#1 → (ins 0).data_pmp_err_i = 0#1 →
    -- cycle 1: the first word arrives; the core supplies `a + 4`; the second request is granted
    (ins 1).adder_result_ex_i = a + 4#32 → (ins 1).data_rvalid_i = 1#1 →
    (ins 1).data_bus_err_i = 0#1 → (ins 1).data_gnt_i = 1#1 → (ins 1).data_pmp_err_i = 0#1 →
    -- cycle 2: the second word arrives; nothing new is issued
    (ins 2).lsu_req_i = 0#1 → (ins 2).data_rvalid_i = 1#1 → (ins 2).data_bus_err_i = 0#1 →
    let o1 := IbexLSU.outputs ((IbexLSU.circuit s).run ins 1) (ins 1)
    let o2 := IbexLSU.outputs ((IbexLSU.circuit s).run ins 2) (ins 2)
    o1.addr_incr_req_o = 1#1 ∧ o1.data_req_o = 1#1 ∧ o1.data_addr_o = LSU.wordAddr a + 4#32 ∧
    o2.lsu_rdata_valid_o = 1#1 ∧
    o2.lsu_rdata_o = LSU.loadWordSpan (ins 1).data_rdata_i (ins 2).data_rdata_i a

/-! ## Challenge (ungraded, no reference proof) -/

/-- **C** The multiplier, connected to the ALU's adder and the ID stage's intermediate
registers, computes the product: after MUL `a b` (any signedness) from idle, the result in
cycle 32 is `a * b`. Checked on 400 random operand pairs by running the model
(`capstone/exam/simcheck.lean`), not proven. A proof needs a loop invariant over the 32
shift-and-add steps; `bv_decide` cannot multiply 32-bit numbers directly. -/
def mul_correct : Prop :=
  ∀ (mode : BitVec 2) (a b : BitVec 32) (x0 : MD.System), x0.md.md_state_q_ff = MD.IDLE →
    MD.sysResult MD.MULL mode a b (MD.sysRun MD.MULL mode a b x0 32) = a * b

end IbexExam.Stmt
