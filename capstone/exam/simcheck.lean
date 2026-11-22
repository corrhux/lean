import RtlProof.Exam.Ibex.Statements

/-!
# Evidence for the challenge statement `Stmt.mul_correct` (not a proof)

Evaluates exactly the statement's two sides, `sysResult … (sysRun … x0 32)` and `a * b`,
for 400 pseudo-random cases: operands, signedness mode, and a random start state (FSM
idle, every other register and both intermediate values random). Also runs MULH against
the 64-bit product's high word. Prints `(failures, cases)`; CI requires 0 failures.
-/

open IbexExam.MD

def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

def mulhSpec (mode : BitVec 2) (a b : BitVec 32) : BitVec 32 :=
  let ea : BitVec 64 := if mode.getLsbD 0 then a.signExtend 64 else a.setWidth 64
  let eb : BitVec 64 := if mode.getLsbD 1 then b.signExtend 64 else b.setWidth 64
  (ea * eb).extractLsb' 32 32

def check : Nat × Nat := Id.run do
  let mut s := 2026
  let mut bad := 0
  let mut n := 0
  for _ in [0:200] do
    let mut r : Array Nat := #[]
    for _ in [0:8] do
      s := lcg s; r := r.push (s / 2 ^ 20)
    let a := BitVec.ofNat 32 r[0]!
    let b := BitVec.ofNat 32 r[1]!
    let mode := BitVec.ofNat 2 r[2]!
    let x0 : System :=
      { md := { md_state_q_ff := IDLE, multdiv_count_q_ff := BitVec.ofNat 5 r[3]!,
                op_b_shift_q_ff := BitVec.ofNat 33 r[4]!, op_a_shift_q_ff := BitVec.ofNat 33 r[5]!,
                div_by_zero_q_ff := BitVec.ofNat 1 r[3]! },
        imd0 := BitVec.ofNat 34 r[6]!, imd1 := BitVec.ofNat 34 r[7]! }
    n := n + 2
    if sysResult MULL mode a b (sysRun MULL mode a b x0 32) != a * b then bad := bad + 1
    if sysResult MULH mode a b (sysRun MULH mode a b x0 32) != mulhSpec mode a b then bad := bad + 1
  return (bad, n)

#eval check
