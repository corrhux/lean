/-!
# Synchronous circuits and their properties

The semantic core shared by every example (docs/ARCHITECTURE.md §4.1).

A `Circuit I S` has an input type `I`, a state type `S`, a reset state and a
next-state function: the `always_ff` block. `run c ins n` is the state after
`n` clock edges from reset when input `ins t` is applied at cycle `t`. An
arbitrary `ins : Nat → I` plays the role of a free input in Jasper.
-/

namespace RtlProof

structure Circuit (I S : Type) where
  /-- reset state -/
  init : S
  /-- next-state function -/
  step : S → I → S

namespace Circuit

variable {I S : Type}

/-- State after `n` cycles from reset. -/
def run (c : Circuit I S) (ins : Nat → I) : Nat → S
  | 0     => c.init
  | n + 1 => c.step (run c ins n) (ins n)

/-- State after `n` cycles from an arbitrary start state `s` (used by induction steps). -/
def runFrom (c : Circuit I S) (s : S) (ins : Nat → I) : Nat → S
  | 0     => s
  | n + 1 => c.step (runFrom c s ins n) (ins n)

/-- SVA `assert property (P)`: `P` holds in every reachable state, for every input stream. -/
def Safe (c : Circuit I S) (P : S → Prop) : Prop :=
  ∀ ins n, P (c.run ins n)

/-- `assert` under `assume`: only input streams satisfying `A` at every cycle are considered. -/
def SafeUnder (c : Circuit I S) (A : S → I → Prop) (P : S → Prop) : Prop :=
  ∀ ins, (∀ n, A (c.run ins n) (ins n)) → ∀ n, P (c.run ins n)

/-- Model-checker semantics of `assume`/`assert` when both may read inputs (immediate
assertions in `always_comb`, as produced by `sv2lean`): at cycle `n`, `P` must hold
whenever the assumptions held at every cycle up to and including `n`. This is the
"prefix" reading that SymbiYosys and Jasper use. It is stronger than requiring the
assumptions on the whole infinite trace, which would excuse a violation at cycle
`n` because of an assumption failing later. -/
def SafePrefix (c : Circuit I S) (A P : S → I → Prop) : Prop :=
  ∀ ins n, (∀ m, m ≤ n → A (c.run ins m) (ins m)) → P (c.run ins n) (ins n)

/-- What a BMC "bounded proof to depth `k`" establishes, which is a weaker theorem than `Safe`. -/
def BoundedSafe (c : Circuit I S) (P : S → Prop) (k : Nat) : Prop :=
  ∀ ins n, n ≤ k → P (c.run ins n)

@[simp] theorem run_zero (c : Circuit I S) (ins : Nat → I) : c.run ins 0 = c.init := rfl

@[simp] theorem run_succ (c : Circuit I S) (ins : Nat → I) (n : Nat) :
    c.run ins (n + 1) = c.step (c.run ins n) (ins n) := rfl

@[simp] theorem runFrom_zero (c : Circuit I S) (s : S) (ins : Nat → I) :
    c.runFrom s ins 0 = s := rfl

@[simp] theorem runFrom_succ (c : Circuit I S) (s : S) (ins : Nat → I) (n : Nat) :
    c.runFrom s ins (n + 1) = c.step (c.runFrom s ins n) (ins n) := rfl

/-- Running from reset is running from the reset state. -/
theorem run_eq_runFrom (c : Circuit I S) (ins : Nat → I) (n : Nat) :
    c.run ins n = c.runFrom c.init ins n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [run_succ, runFrom_succ, ih]

end Circuit
end RtlProof
