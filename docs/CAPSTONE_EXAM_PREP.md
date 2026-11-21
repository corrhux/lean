# Capstone exam prep: what you need to verify the rest of Ibex yourself

The capstone so far proved Ibex's *combinational* blocks against the ISA: the ALU,
the decoders, the register file's one-cycle behaviour. What is left is sequential:
the **load/store unit** (a bus protocol and a small FSM), the **iterative
multiplier/divider** (32 cycles of shift-and-add that borrow the ALU's adder), and
the pipeline around them. Those need ideas that the earlier chapters only touched.
This module teaches them on small circuits, then you prove the real thing in the
**Ibex exam** (`RtlProof/Exam/Ibex/`), graded by `pvs-exam`.

| Chapter | Idea | Jasper equivalent | Exam items |
|---|---|---|---|
| E5 | Reading a generated model: asynchronous reset, `x`, packed arrays | reading the elaborated netlist | all |
| E6 | One-step rules and reachability invariants | helper assertions for induction | M1, L1, L2 |
| E7 | Counting cycles: induction over time, unbounded waits | depth of BMC vs. a full proof | M2, M3, L3 |
| E8 | Two runs: non-interference | two instances, assume equal control | M4 |
| E9 | Refinement and composition | end-to-end checks across blocks | L4, challenge |
| E10 | Track 1 practical: Ibex against Sail, in Jasper | Ibex's own `dv/formal` flow | (practical) |
| E11 | Track 3 outline: the pipeline | Burch–Dill / flushing | (not examined) |

The worked examples below compile in CI, in this order (`tools/lean_blocks.py`).
They use small hand-written circuits so that they teach the technique without
solving an exam item.

```lean
import RtlProof.Core.Circuit
import RtlProof.Meta.Induction
import RtlProof.Exam.Ibex.Spec
import Std.Tactic.BVDecide
open RtlProof
```

## The exam

| Item | Points | Statement (in `Statements.lean`) |
|---|---|---|
| M1 | 10 | `md_state_valid`: Ibex's assertion `IbexMultDivStateValid` holds in every reachable state |
| M2 | 15 | `mul_latency`: a multiply raises `valid_o` exactly in cycle 32 |
| M3 | 10 | `div_latency`: a divide raises it exactly in cycle 36 |
| M4 | 20 | `constant_time`: with `data_ind_timing_i`, timing does not depend on the operands (Ibex `SEC_CM: CORE.DATA_REG_SW.SCA`) |
| L1 | 5 | `lsu_req_held`: a bus request is held until granted |
| L2 | 15 | `lsu_store`: in every reachable state, a store writes the bytes SB/SH/SW write |
| L3 | 15 | `lsu_load`: a load returns the ISA's value however many cycles memory takes |
| L4 | 10 | `lsu_load_misaligned`: a misaligned LW is split in two bus transactions and still returns the ISA's value |
| challenge | – | `mul_correct`: the multiplier, wired to the ALU's adder, computes `a * b` (no reference proof; checked on 400 random cases) |

How to work:

```sh
lake build                       # once: builds the models and statements
pvs-exam                         # grade RtlProof/Exam/Ibex/MultDiv.lean and LoadStore.lean
pvs-app                          # or: the web app; open your exam file in the Lean scratchpad
```

Rules the grader enforces: your theorem must have exactly the statement in
`Statements.lean` (it checks `example : Stmt.X := X`); the proof may use any tactic,
and `bv_decide`'s certificates are trusted (as everywhere in this course), but not
`sorry`, `native_decide` or an `axiom` of your own; and `Spec.lean`,
`Statements.lean` and the generated models must be unchanged (checked by hash).
Reference solutions exist, in `capstone/exam/solutions/`. They are spoilers; CI uses
them to make sure every statement is provable.

## E5 Reading a generated model

You will spend more time reading `RtlProof/Generated/IbexMD.lean` and
`IbexLSU.lean` than writing proofs. Four things to know.

**`step`, `comb`, `outputs`.** `comb s i` computes every combinational signal of the
cycle from the registers `s` and the inputs `i`; `step s i` is the registers after
the clock edge; `outputs s i` the output ports this cycle. A proof about one cycle
almost always starts with `simp only [outputs, step, comb] at *` (unfolding them into
one big bit-vector formula) and ends with `bv_decide`.

**Asynchronous reset gives every register two names.** Ibex resets with `rst_ni`
asynchronously. Yosys's `async2sync` turns that into a plain flop followed by a mux,
so the model has the flop (`md_state_q_ff`, a field of `State`) and the value the RTL
reads (`md_state_q`, in `comb`), which is the reset value while `rst_ni = 0`:

```lean
namespace PrepE5
open Gen.IbexMD

-- What the RTL reads during reset, whatever the flop holds:
example (s : State) (i : Input) (h : i.rst_ni = 0#1) : (comb s i).md_state_q = 0#3 := by
  simp only [comb] at *
  bv_decide

-- Out of reset it is the flop:
example (s : State) (i : Input) (h : i.rst_ni = 1#1) : (comb s i).md_state_q = s.md_state_q_ff := by
  simp only [comb] at *
  bv_decide

end PrepE5
```

That is why every exam statement says `rst_ni = 1` for the cycles it talks about,
and why the statements are about the `_ff` fields.

**`x` becomes an input.** Wherever the RTL assigns `'x` (a "don't care", typically in
`default:` branches), the model has a free input `undef_k`. A theorem proved for all
inputs therefore holds whatever value synthesis picks for each `x`: stronger than a
simulator, which picks one. If a proof fails because of an `undef_k`, the design
really does depend on a don't-care there.

**Unpacked arrays are packed by sv2v, element 0 in the high bits.** Ibex's
`imd_val_q_i[2]` (two 34-bit values) arrives as one 68-bit input. Check such things
by evaluating rather than guessing:

```lean
#eval ((0x1#34 ++ 0x2#34 : BitVec 68).extractLsb' 34 34)   -- element 0: 0x1
```

The challenge's `MD.sysInput` relies on exactly this.

## E6 One-step rules and reachability invariants

**A one-step rule needs no induction.** "While waiting for a grant the request stays
high" talks about one cycle and holds in *every* state, reachable or not. Prove it
for all states and inputs, in one `bv_decide`. (Jasper would prove it at depth 1.)

**Most properties only hold in reachable states.** Here is a small unit with two
states, READY (1) and BUSY (2), and a `pend` flag. Like the RTL it is modelled on, an
illegal state (0 or 3) falls back to READY, and keeps `pend` as it is.

```lean
namespace PrepE6

structure S where
  st : BitVec 2
  pend : BitVec 1

structure I where
  go : BitVec 1
  done : BitVec 1

/-- Field by field, as `sv2lean` writes it: each register's next value is one expression. -/
def step (s : S) (i : I) : S :=
  { st := if s.st = 1#2 then (if i.go = 1#1 then 2#2 else 1#2)
          else if s.st = 2#2 then (if i.done = 1#1 then 1#2 else 2#2)
          else 1#2,
    pend := if s.st = 1#2 then (if i.go = 1#1 then 1#1 else s.pend)
            else if s.st = 2#2 then (if i.done = 1#1 then 0#1 else s.pend)
            else s.pend }

def unit : Circuit I S := ⟨{ st := 1#2, pend := 0#1 }, step⟩

/-- The property: when READY, nothing is pending. -/
def P (s : S) : Prop := s.st = 1#2 → s.pend = 0#1

end PrepE6
```

`P` is true in every reachable state, but it is **not inductive**: a state that
satisfies it can step to one that does not. `bv_decide` shows you which:

```lean fails
open PrepE6 in
example (s : S) (i : I) (h : P s) : P (step s i) := by
  simp only [P, step] at *
  bv_decide
```

The counterexample has `st = 3` (or 0) and `pend = 1`: illegal, so `P` holds vacuously,
and the next state is READY with `pend` still set. No reachable state looks like that.
This is Jasper's "induction failed from an unreachable state", and the fix is the same:
add what you know about reachable states (Jasper: a helper assertion) until the
claim becomes inductive.

```lean
namespace PrepE6

def Inv (s : S) : Prop := (s.st = 1#2 ∨ s.st = 2#2) ∧ P s

theorem inv_step (s : S) (i : I) (h : Inv s) : Inv (step s i) := by
  simp only [Inv, P, step] at *
  bv_decide

theorem p_safe : unit.Safe P :=
  Circuit.induction_sound unit P Inv (by simp only [Inv, P, unit]; decide)
    (fun s i h => inv_step s i h) (fun _ h => h.2)

end PrepE6
```

`Circuit.induction_sound` (proved in `RtlProof/Meta/Induction.lean`) is the
induction rule: invariant holds initially, is preserved, and implies the property.
The exam's L2 needs exactly this kind of invariant; find it by reading the
counterexample to the one-step claim.

## E7 Counting cycles

A model checker shows "`valid` rises at cycle 32" by BMC to depth 33, and "the answer
comes back however long memory takes" not at all without a bound on the wait. Lean
proves both by **induction over time**. The pattern: describe the state at cycle
`m + j` with a predicate, prove one step preserves it, and induct on `j`.

A countdown timer: `start` loads 7; each cycle counts down to 0; `done` is high when
the count is 0.

```lean
namespace PrepE7

structure S where
  cnt : BitVec 3

structure I where
  start : BitVec 1

def step (s : S) (i : I) : S :=
  { cnt := if i.start = 1#1 then 7#3 else if s.cnt = 0#3 then 0#3 else s.cnt - 1#3 }

def done (s : S) : BitVec 1 := if s.cnt = 0#3 then 1#1 else 0#1

/-- One step, in arithmetic terms: a non-zero count goes down by one. -/
theorem step_down (s : S) (i : I) (hi : i.start = 0#1) (h : s.cnt ≠ 0#3) :
    (step s i).cnt = s.cnt - 1#3 := by
  simp only [step] at *
  bv_decide

/-- After `start`, cycle `1 + j` has count `7 - j` (as a number), for `j ≤ 7`. -/
theorem phase (r : Nat → S) (ins : Nat → I) (hr : ∀ n, r (n + 1) = step (r n) (ins n))
    (h0 : (ins 0).start = 1#1) (hrest : ∀ n, 1 ≤ n → (ins n).start = 0#1) :
    ∀ j, j ≤ 7 → (r (1 + j)).cnt.toNat = 7 - j := by
  intro j
  induction j with
  | zero => intro _; rw [hr]; simp [step, h0]
  | succ j ih =>
    intro hj
    have hc := ih (by omega)
    have hne : (r (1 + j)).cnt ≠ 0#3 := by
      intro h; rw [h] at hc; simp at hc; omega
    rw [show 1 + (j + 1) = (1 + j) + 1 by omega, hr, step_down _ _ (hrest _ (by omega)) hne,
      BitVec.toNat_sub, hc]
    simp; omega

end PrepE7
```

Three details you will meet in the exam:

* **Count in `Nat`, step in `BitVec`.** `bv_decide` proves the one-step fact
  (`cnt - 1`); the induction is about `toNat`, where `omega` does the arithmetic.
  `BitVec.toNat_sub` translates, `BitVec.eq_of_toNat_eq` translates back.
* **`r (n + 1)` *is* `step (r n) (ins n)`**, by definition (`rfl`), but `rw` only
  rewrites what it sees. Use `hr` as above, or state a fact about `r (n + 1)` with
  `have h : P (r (n + 1)) := lemma …`, which Lean accepts by unfolding.
* **Unbounded waits** are the same pattern with a predicate instead of a count: "a
  request is outstanding with these attributes" is preserved by every idle cycle;
  induct on the number of idle cycles; then show what the answering cycle outputs.

## E8 Two runs: non-interference

"Timing does not depend on secret data" is not a property of one run: it compares
two. Jasper checks it on two instances of the design with control inputs assumed
equal; in Lean you write the two runs side by side. The proof has the same shape as
E7: a one-step lemma **about two copies** ("equal control state and equal control
inputs give equal control state next cycle"), then induction.

A divider that may finish early when the dividend is small, unless told not to:

```lean
namespace PrepE8

structure S where
  busy : BitVec 1
  cnt : BitVec 4
  x : BitVec 8          -- data

structure I where
  go : BitVec 1
  fixed : BitVec 1      -- "data-independent timing"
  d : BitVec 8          -- data

def step (s : S) (i : I) : S :=
  { busy := if s.busy = 0#1 then i.go
            else if s.cnt = 0#4 ∨ (i.fixed = 0#1 ∧ s.x < 16#8) then 0#1 else 1#1,
    cnt := if s.busy = 0#1 then 15#4 else s.cnt - 1#4,
    x := if s.busy = 0#1 then i.d else s.x >>> 1 }

def ctl (s : S) : BitVec 1 × BitVec 4 := (s.busy, s.cnt)

theorem ctl_step (s t : S) (i j : I) (hs : ctl s = ctl t) (hgo : i.go = j.go)
    (hf : i.fixed = 1#1) (hf' : j.fixed = 1#1) : ctl (step s i) = ctl (step t j) := by
  simp only [ctl, step, Prod.mk.injEq] at *
  obtain ⟨h1, h2⟩ := hs
  bv_decide

end PrepE8
```

Without `fixed` the same lemma is false, and `bv_decide`'s counterexample is the
leak: two runs that differ only in the data `x`, one of which finishes early.

```lean fails
open PrepE8 in
example (s t : S) (i j : I) (hs : ctl s = ctl t) (hgo : i.go = j.go) (hf : i.fixed = j.fixed) :
    ctl (step s i) = ctl (step t j) := by
  simp only [ctl, step, Prod.mk.injEq] at *
  obtain ⟨h1, h2⟩ := hs
  bv_decide
```

Which inputs count as "control" is part of the statement, and the important design
decision: in the exam it is `MD.ctlIn`. Everything not in it, including what the
ALU hands back, may differ between the two runs.

## E9 Refinement and composition

**State the spec in terms of what the system means, not its signals.** "The byte
enables are `0011`" checks one encoding; "memory ends up holding what SB/SH/SW say" is
the ISA's meaning, and is the statement that survives a redesign. The exam's
`LSU.busWrite` turns the bus signals into their effect on a memory word, and
`LSU.storeSpec` is the ISA's effect; the theorem says they agree for every old memory
word. The same goes for loads: `LSU.loadSpec` picks the bytes and extends them.

```lean
open IbexExam.LSU in
-- A byte store at offset 2 changes byte 2 of the word and nothing else:
example (old v : BitVec 32) :
    storeSpec old 0x1002#32 2#2 v = (old &&& 0xFF00FFFF#32) ||| ((v &&& 0xFF#32) <<< 16) := by
  simp only [storeSpec, sizeMask, bits, off]
  bv_decide
```

**A multi-cycle implementation refines a one-step spec.** A misaligned word load is
one step for the ISA and two bus transactions for Ibex. Run the implementation for
its cycles, then compare the result with the one-step spec. A small version: an
8-bit adder that works a nibble per cycle and must equal `+`.

```lean
namespace PrepE9

structure S where
  lo : BitVec 4
  carry : BitVec 1

/-- Cycle 1: add the low nibbles, keep the carry. Cycle 2: add the high nibbles. -/
def cycle1 (a b : BitVec 8) : S :=
  let t := (a.setWidth 4).setWidth 5 + (b.setWidth 4).setWidth 5
  { lo := t.setWidth 4, carry := t.extractLsb' 4 1 }

def cycle2 (s : S) (a b : BitVec 8) : BitVec 8 :=
  let hi := (a.extractLsb' 4 4) + (b.extractLsb' 4 4) + s.carry.setWidth 4
  hi ++ s.lo

theorem refines (a b : BitVec 8) : cycle2 (cycle1 a b) a b = a + b := by
  simp only [cycle1, cycle2]
  bv_decide

end PrepE9
```

**Composition: when a block borrows another's resources.** `ibex_multdiv_slow` does
not add by itself: it hands two operands to the ALU and reads the sum back, and keeps
its running sum in the ID stage's `imd_val_q` registers. To say anything about its
*result* you connect the three: `MD.sysStep` in `Spec.lean` does it, by computing the
operands first (they do not depend on the sum, so there is no combinational loop),
then the ALU, then the multiplier's next state and the registers' write enables.
Before proving anything about a composition, run it:

```lean
open IbexExam.MD in
#eval
  let x0 : System := { md := Gen.IbexMD.init0, imd0 := 0, imd1 := 0 }
  sysResult MULL 0 1234#32 5678#32 (sysRun MULL 0 1234#32 5678#32 x0 32) == 1234#32 * 5678#32
```

**The challenge** asks for the result in general. `bv_decide` cannot multiply 32-bit
numbers (see Part D: the miters blow up), so the proof needs a loop invariant over
the 32 shift-and-add cycles, like the course's multiplier twin (`RtlProof.Mul.acc_eq_mul`,
by induction on the width). Expect to state "after `j` cycles the running sum is the
partial product of `a` and the low `j` bits of `b`" in `Nat` (`toNat`), with care for
the Baugh–Wooley correction bits Ibex adds for signed operands (`op_a_bw_pp`). There
is no reference proof: this one is open.

## E10 Track 1 practical: Ibex against Sail, in Jasper

Ibex ships its own end-to-end proof that the core's retired instructions match the
Sail RISC-V model: `third_party/ibex/dv/formal/` (read its `README.md` and
[CAPSTONE_PRIMER.md](CAPSTONE_PRIMER.md) for what RVFI and Sail are). It runs in
**Jasper**, or with Yosys and rIC3 for open-source tools; both need Nix and a large
machine (the README cites 128 GiB of RAM and 32 cores). It cannot run in this
course's container, so the practical is for your own machine:

1. `cd third_party/ibex/dv/formal && nix develop .#formal`, then `make jg` to open
   Jasper with the flow loaded.
2. In the Task Tree, prove the steps in order. Note which steps are *lemmas* (helper
   properties proved first and assumed later) and which are the end-to-end property.
3. Break the RTL: in `rtl/ibex_alu.sv` swap the operands of SUB, rerun, and find the
   Sail mismatch in the counterexample trace. Compare with what the Track 2 Lean
   proof of the ALU says about the same bug.
4. Write down, for one instruction (say LW), which properties in this flow
   correspond to the exam's L3 and L4, and what the flow assumes about the bus that
   the exam states explicitly.

## E11 Track 3 outline: the pipeline (not examined)

The last step, "the whole core executes the ISA", is a refinement between a
pipelined implementation and a one-instruction-at-a-time spec. The classical method
(Burch and Dill, 1994) relates them by **flushing**: run the pipeline without new
instructions until it is empty, then compare the architectural state with the spec's
after the same instructions. Stated in this course's terms it would be a theorem
about `ibex_core` with an abstraction function from pipeline state to `(pc, x1..x31,
memory)`. It is out of reach here for practical reasons, not conceptual ones:
`ibex_core` is thousands of cells, the commit point of each instruction depends on
stalls and the LSU, and the proof needs invariants about every in-flight
instruction. Ibex's Jasper flow (E10) is the industrial answer; the exam's pieces
(E6–E9) are the building blocks it uses.

Reading: Burch & Dill, *Automatic verification of pipelined microprocessor control*
(CAV 1994); the Ibex formal flow's `README.md`; and, for processor refinement in a
proof assistant (Coq), Kami and Kôika. All are listed in [REFERENCES.md](REFERENCES.md).
