# Lean Fluency — the language and its semantics, in plain terms

Course **Part C** (expanded). Audience: an RTL formal-verification expert with
no functional-programming or theorem-proving background. Goal: read and write
Lean 4 proofs fluently enough to do Parts D and E without looking things up
every line.

Target version: **Lean 4.36** (core Lean only, no Mathlib).
**Code status:** written for this version but **not yet compiled**; every block
will be checked by CI (SPEC FR-C2) and moved into
`RtlProof/Fluency/L*.lean` exercise/solution files. Expect small fixes when
that happens.

---

## How to use this module

Each lesson has the same parts:

- **Idea** — the concept in one or two plain sentences.
- **Hardware picture** — the closest thing you already know from RTL/Jasper.
- **Code** — small, runnable examples. Type them in; don't just read them.
- **What you'll see** — what the editor's infoview shows.
- **Traps** — the mistakes everyone makes.
- **Drill** — short exercises (solutions in Appendix C).

Work in VS Code with the official Lean 4 extension. The **infoview** (right
pane) is the most important tool you have: it shows values, types, and — in
proofs — the current **goal**. Keep it open, always.

| Lesson | Topic | You can do afterwards |
|---|---|---|
| L0 | Mental model | Explain what Lean is and what "checked" means |
| L1 | Expressions, types, functions | Read any Lean expression |
| L2 | Definitions, `let`, `if`, `match`, recursion | Write combinational and recursive functions |
| L3 | Data: `structure`, `inductive`, namespaces | Model registers, enums, instruction ASTs |
| L4 | Bit vectors for hardware | Model datapaths with exact widths |
| L5 | Implicit arguments, type classes, coercions | Understand "failed to synthesize" errors |
| L6 | Propositions: `Prop` vs `Bool` | Write correct property statements |
| L7 | Proofs are programs (Curry–Howard, simplified) | Write small proofs without tactics |
| L8 | How Lean computes: definitional equality | Predict when `rfl` works |
| L9 | Tactic mode: goals and the core tactics | Drive a proof interactively |
| L10 | Equality and rewriting: `rw`, `simp` | Transform goals deliberately |
| L11 | Logic tactics: cases, existentials, contradiction | Handle every connective |
| L12 | Induction | Prove facts about recursive definitions and traces |
| L13 | Decision procedures: `decide`, `omega`, `bv_decide`, `grind` | Delegate the boring parts, know the trust cost |
| L14 | Modelling a circuit end to end | Prove a real invariant of a sequential design |
| L15 | Organising proofs | Write lemmas, simp sets, namespaces like a pro |
| L16 | Reading errors and getting unstuck | Debug any failing proof |
| L17 | Semantics under the hood (simplified) | Understand elaboration, universes, the kernel |
| App. A | Cheat sheets | — |
| App. B | Unicode input | — |
| App. C | Drill solutions | — |

---

## L0 — Mental model

**Idea.** Lean is *one* language that is simultaneously:
1. a **functional programming language** (you can define and run functions), and
2. a **proof checker** (you can state facts about those functions and prove them).

A proof in Lean is not a search result; it is an **object** you build (by hand
or with help from tactics) and that a small, trusted **kernel** checks.

**Hardware picture.**

| You know | Lean |
|---|---|
| RTL module | function (`def`) |
| Simulation | evaluation (`#eval`) |
| SVA assertion expression | proposition (a value of type `Prop`) |
| Engine says "proven" | kernel accepts a proof term |
| "Undetermined" / waived | `sorry` (a hole; Lean warns loudly) |
| Engine's trust base | Lean's kernel (+ anything listed by `#print axioms`) |

**Three commands you'll use constantly:**

```lean
#eval 2 + 3          -- run it: 5
#check 2 + 3         -- what type is it? 2 + 3 : Nat
#print Nat.add       -- show the definition
```

**Traps.** Lean is whitespace- and indentation-sensitive inside `by` blocks and
`match` arms. Use spaces, not tabs.

---

## L1 — Expressions, types, functions

**Idea.** Every expression has exactly one **type**. Functions are applied by
writing arguments after them, separated by spaces — no parentheses or commas.

```lean
#check (5 : Nat)                 -- natural numbers 0,1,2,... (unbounded)
#check (-5 : Int)                -- integers
#check true                      -- Bool
#check "hello"                   -- String
#check Nat.succ                  -- Nat → Nat
#check Nat.add                   -- Nat → Nat → Nat

#eval Nat.add 2 3                -- 5     (not Nat.add(2, 3))
#eval Nat.succ (Nat.succ 0)      -- 2     parentheses only for grouping
```

**Arrows.** `Nat → Nat → Nat` means "takes a `Nat`, then another `Nat`, returns
a `Nat`". Arrows associate to the right: `Nat → (Nat → Nat)`. So a
two-argument function is really a function that returns a function
(**currying**). This lets you supply arguments one at a time:

```lean
def add3 : Nat → Nat := Nat.add 3    -- partially applied
#eval add3 10                         -- 13
```

**Anonymous functions** (lambdas):

```lean
#eval (fun x => x * 2) 21            -- 42
#eval [1, 2, 3].map (fun x => x * 2) -- [2, 4, 6]
#eval [1, 2, 3].map (· * 2)          -- same; `·` is "the argument"
```

**Hardware picture.** `fun x => x * 2` is an anonymous combinational block.
Currying is like tying off some inputs of a module to constants.

**Traps.**
- `f x + 1` means `(f x) + 1`. Application binds tightest.
- Negative literals need parentheses: `f (-1)`, not `f -1` (that's `f - 1`).
- `Nat` subtraction truncates at zero: `#eval (3 : Nat) - 5` gives `0`. Use `Int` if you need negatives. This trips up everyone once.

**Drill L1.** (a) What is the type of `fun (x : Nat) (y : Nat) => x + y`?
(b) Evaluate `[10, 20, 30].map (· + 1)`. (c) Why does `#eval (2 : Nat) - 3`
print `0`?

---

## L2 — Definitions, `let`, `if`, `match`, recursion

### Definitions

```lean
def double (x : Nat) : Nat := x * 2
--  name   input     output  body

def mux (sel : Bool) (a b : Nat) : Nat :=
  if sel then a else b

#eval mux true 1 2    -- 1
```

The return type after the colon is optional when Lean can infer it, but write
it anyway: it documents intent and gives better error messages.

### Local names: `let` and `where`

```lean
def hyp (a b : Nat) : Nat :=
  let a2 := a * a
  let b2 := b * b
  a2 + b2

def area (w h : Nat) : Nat := helper w * h
where helper (x : Nat) := x + 1
```

### Pattern matching

`match` is a `case` statement that Lean checks for **completeness** — a missing
case is a compile error, not a latch.

```lean
inductive St where
  | idle | req | ack | done

def stName (x : St) : String :=
  match x with
  | .idle => "IDLE"
  | .req  => "REQ"
  | .ack  => "ACK"
  | .done => "DONE"
```

(`inductive` is explained in L3; `.idle` is short for `St.idle` when Lean
knows the type.)

You can match directly in the definition's arguments:

```lean
def isZero : Nat → Bool
  | 0     => true
  | _ + 1 => false        -- `_` = "don't care"
```

### Recursion

```lean
def sumTo : Nat → Nat
  | 0     => 0
  | n + 1 => (n + 1) + sumTo n

#eval sumTo 10   -- 55
```

Lean must be sure every recursive function **terminates** (otherwise you could
"prove" anything with an infinite loop). For structural recursion (calling
yourself on a smaller piece, like `n` from `n + 1`) Lean figures it out. For
other shapes you give a measure:

```lean
def countUp (i n : Nat) : Nat :=
  if h : i < n then countUp (i + 1) n + 1 else 0
termination_by n - i
```

**Hardware picture.** Structural recursion over `n` is a `generate for` loop
unrolled `n` times — but for *every* `n` at once.

**Traps.**
- `partial def` turns off the termination check, but then you **cannot prove
  anything** about the function. Avoid it for anything you want to verify.
- `if c then … else …` needs `c` to be a `Bool` or a *decidable* `Prop` (see L6).

**Drill L2.** (a) Define `pow2 : Nat → Nat` with `pow2 0 = 1`,
`pow2 (n+1) = 2 * pow2 n`. (b) Define `popcount : List Bool → Nat`.
(c) What error do you get if you delete the `| .done => "DONE"` line from `stName`?

---

## L3 — Data: `structure`, `inductive`, namespaces

### Structures — records / packed structs

```lean
structure Regs where
  pc  : Nat
  acc : Nat
  zf  : Bool
deriving Repr

def r0 : Regs := { pc := 0, acc := 0, zf := true }
def r1 : Regs := ⟨4, 7, false⟩          -- anonymous constructor, field order
def r2 : Regs := { r1 with acc := 9 }   -- copy with one field changed

#eval r2.acc    -- 9
#eval r2        -- { pc := 4, acc := 9, zf := false }
```

`deriving Repr` lets `#eval` print it. Add `DecidableEq` if you want to compare
values with `=` inside `if` or `decide`.

### Inductive types — enums and tagged unions

```lean
inductive AluOp where
  | add | sub | land | lor | lxor
deriving Repr, DecidableEq

inductive Instr where
  | alu  (op : AluOp) (rd rs1 rs2 : Fin 32)
  | addi (rd rs1 : Fin 32) (imm : Int)
  | halt
deriving Repr
```

An `inductive` lists the **only** ways to build a value. That's what makes
`match` completeness checking possible, and it's what `cases` and `induction`
use in proofs.

### Namespaces and dot notation

```lean
namespace AluOp
def isLogic : AluOp → Bool
  | .land | .lor | .lxor => true
  | _                    => false
end AluOp

#eval AluOp.isLogic .lor     -- true
#eval (AluOp.lor).isLogic    -- same: dot notation finds AluOp.isLogic
```

`x.f` means "look for `f` in the namespace of `x`'s type and pass `x` to it".
That's why `xs.length`, `s.pc` and `v.toNat` all work.

**Hardware picture.** `structure` ≈ `typedef struct packed`; `inductive` with
no arguments ≈ `typedef enum`; with arguments ≈ a tagged union (an instruction
format with different fields per opcode).

**Traps.** Field order matters for `⟨…⟩`. Prefer `{ field := … }` when there
are more than two fields.

**Drill L3.** (a) Define `structure FifoState` with `rd wr : Fin 8` and
`count : Nat`. (b) Add an `AluOp.slt` constructor and see which `match`es
break. (c) Write `Instr.dest : Instr → Option (Fin 32)`.

---

## L4 — Bit vectors for hardware

**Idea.** `BitVec n` is an `n`-bit vector. The width is **part of the type**, so
width mismatches are type errors, not lint warnings. Arithmetic wraps modulo
2ⁿ exactly like RTL.

```lean
#check (5#8 : BitVec 8)       -- literal: value 5, width 8
#check 0xFF#8
#eval 200#8 + 100#8           -- 44  (300 mod 256)
#eval (0#8) - 1#8             -- 255
#eval (5#8).toNat             -- 5   as an unbounded Nat
#eval BitVec.ofNat 8 300      -- 44

-- bitwise
#eval 0b1100#4 &&& 0b1010#4   -- 0b1000
#eval 0b1100#4 ||| 0b1010#4   -- 0b1110
#eval 0b1100#4 ^^^ 0b1010#4   -- 0b0110
#eval ~~~0b1100#4             -- 0b0011
#eval 0b0001#4 <<< 2          -- 0b0100
#eval 0b1000#4 >>> 3          -- 0b0001   (logical shift)

-- slicing, concatenation, extension
#eval (0xAB#8).extractLsb 7 4           -- upper nibble: 0xA, width 4
#eval (0xA#4) ++ (0xB#4)                -- 0xAB, width 8
#eval (0x80#8).signExtend 16            -- 0xFF80
#eval (0x80#8).zeroExtend 16            -- 0x0080
#eval (0x80#8).getLsbD 7                -- true   (bit 7)

-- comparisons (Bool-valued)
#eval (0x80#8).ult 0x01#8               -- false  unsigned: 128 < 1
#eval (0x80#8).slt 0x01#8               -- true   signed:  -128 < 1
```

(The exact printed format of `#eval` on `BitVec` varies between versions —
hex or decimal; the *values* above are what matter.)

**Width arithmetic is checked.** `(x : BitVec 4) ++ (y : BitVec 4)` has type
`BitVec (4 + 4)`, which Lean knows equals `BitVec 8`. If you write a function
generic in `n`, Lean tracks widths symbolically:

```lean
def swapHalves {n : Nat} (x : BitVec (2 * n)) : BitVec (2 * n) :=
  x.rotateLeft n
```

**`Fin n`** is "a natural number less than `n`" — perfect for register
indices and FIFO pointers. `(5 : Fin 32)`; arithmetic wraps mod `n`.

**Hardware picture.** `BitVec 32` ≈ `logic [31:0]`, but there is no X/Z: every
bit is 0 or 1. (X-propagation semantics must be modelled explicitly if you
need it.)

**Traps.**
- `5#8` is a `BitVec 8`; plain `5` is a `Nat` unless the expected type says
  otherwise. When Lean complains about mismatched types, annotate:
  `(5 : BitVec 8)`.
- `<` and `≤` on `BitVec` are **unsigned** propositions; use `.slt`/`.sle` for
  signed.

**Drill L4.** (a) Write `signBit (x : BitVec 32) : Bool`. (b) Write the RISC-V
I-type immediate extraction: from `instr : BitVec 32`, bits `[31:20]`,
sign-extended to 32. (c) Predict `(0xFFFF#16).signExtend 32 |>.toNat`.

---

## L5 — Implicit arguments, type classes, coercions

### Implicit arguments `{…}`

```lean
def ident {α : Type} (x : α) : α := x
#eval ident 5          -- Lean fills α := Nat itself
#check @ident          -- `@` shows/allows explicit filling: @ident Nat 5
```

Braces mean "Lean will work this out from the other arguments". You'll see
`{n : Nat}` on nearly every `BitVec` lemma: the width is inferred.

### Type classes `[…]`

A type class is an interface; an instance is an implementation for a type.

```lean
#check @HAdd.hAdd    -- what `+` really is
def twice {α : Type} [Add α] (x : α) : α := x + x
#eval twice 21        -- 42 (Nat's Add instance)
#eval twice (21#8)    -- 42 (BitVec 8's Add instance)
```

Square brackets mean "Lean will *search* for an instance". The classes you'll
meet most: `Add`, `Mul`, `OfNat` (number literals), `DecidableEq`,
`Decidable` (can this `Prop` be evaluated?), `Repr` (printing), `Inhabited`.

### Coercions

Lean inserts conversions automatically in some places, shown as `↑x` in goals:

```lean
def n : Nat := 5
def i : Int := n       -- coerced: ↑n
```

**Traps.**
- **"failed to synthesize instance"** means the search for a `[…]` argument
  failed — usually a missing `deriving DecidableEq`/`Repr`, or a type you
  didn't intend.
- A `↑` in a goal is a real function application. `simp` and `omega` handle
  the common Nat/Int ones; if a proof is stuck, look for hidden casts.

**Drill L5.** (a) Remove `deriving Repr` from `Regs` and `#eval r0` — read the
error. (b) Write `max3 {α} [Max α] (a b c : α) : α`.

---

## L6 — Propositions: `Prop` vs `Bool`

**Idea.** A `Bool` is a **value** (a wire is 0 or 1). A `Prop` is a
**statement** that may or may not be provable. `2 + 2 = 4` is a `Prop`;
`true` is a `Bool`.

```lean
#check 2 + 2 = 4                 -- Prop
#check ∀ n : Nat, n + 0 = n      -- Prop
#check ∃ n : Nat, n > 100        -- Prop
#check (2 + 2 == 4)              -- Bool   (== is the Bool test)
```

| Connective | Meaning | Type in |
|---|---|---|
| `p ∧ q` | and | `\and` |
| `p ∨ q` | or | `\or` |
| `¬ p` | not (`p → False`) | `\not` |
| `p → q` | implies | `\to` |
| `p ↔ q` | iff | `\iff` |
| `∀ x, P x` | for all | `\forall` |
| `∃ x, P x` | exists | `\exists` |
| `a = b`, `a ≠ b` | equality | `\ne` |
| `True`, `False` | trivially true / false | |

**Why two kinds?** Some statements can't be computed — "for all `n : Nat`" has
infinitely many cases. Props can talk about infinite things; Bools can't.
A Prop that *can* be computed is called **decidable**; then you can use it in
`if` and prove it with `decide`.

**Bridging.** `b = true` turns a `Bool` into a `Prop`. Lean does this
automatically when you use a `Bool` where a `Prop` is expected (you'll see
`b = true` in goals).

**Hardware picture.**

| SVA | Lean |
|---|---|
| `assert property (a -> b)` | `a → b` (but quantified over all cycles: see L14) |
| `a |-> ##1 b` | statement about `run … (n+1)` given `run … n` |
| `$stable(x)` | `(run c ins (n+1)).x = (run c ins n).x` |
| `cover property (p)` | `∃ ins n, p (run c ins n)` |

**Traps.**
- Don't write `if p then` for a `p : Prop` that isn't decidable — Lean will say
  "failed to synthesize Decidable".
- In theorem statements prefer `x = y` (Prop) to `x == y` (Bool). Lemmas and
  tactics are built around `=`.

**Drill L6.** Write these as Lean Props: (a) "every 8-bit value plus zero is
itself"; (b) "there is a 4-bit value that equals its own negation, other than
zero"; (c) "if the FIFO count is 8 then `full` is true".

---

## L7 — Proofs are programs (Curry–Howard, simplified)

**Idea.** In Lean, **a proposition is a type, and a proof of it is a value of
that type.** Proving `p` means constructing *something* whose type is `p`.
`h : p` reads "`h` is evidence for `p`".

That one idea explains every rule:

| To prove… | Construct… | Because |
|---|---|---|
| `p → q` | a **function** from evidence of `p` to evidence of `q` | implication = transformation |
| `p ∧ q` | a **pair** `⟨hp, hq⟩` | need both |
| `p ∨ q` | `Or.inl hp` or `Or.inr hq` | one side, tagged |
| `∀ x, P x` | a function taking any `x` and returning a proof of `P x` | works for every input |
| `∃ x, P x` | a pair `⟨witness, proof⟩` | show one that works |
| `True` | `trivial` | nothing to show |
| `¬ p` | a function from `p` to `False` | "`p` leads to absurdity" |
| `a = a` | `rfl` | reflexivity |

```lean
theorem and_swap (p q : Prop) (h : p ∧ q) : q ∧ p :=
  ⟨h.2, h.1⟩                       -- a pair built from h's two halves

theorem modus_ponens (p q : Prop) (hp : p) (hpq : p → q) : q :=
  hpq hp                           -- apply the function to the evidence

theorem exists_big : ∃ n : Nat, n > 100 :=
  ⟨101, by decide⟩                 -- witness 101, plus proof that 101 > 100
```

`theorem` is just `def` for proofs. `example` is an anonymous `theorem` you use
for practice.

**Hardware picture.** A helper assertion that you've proven and then *use* as
an assumption is exactly passing `hp` into a function expecting `p`.

**Traps.** `⟨…⟩` is overloaded: it builds whatever structure the expected type
needs (pairs, existentials, structures). If Lean doesn't know the expected
type, it can't use it.

**Drill L7.** Without tactics: (a) `example (p q : Prop) : p → q → p`;
(b) `example (p q r : Prop) (hpq : p → q) (hqr : q → r) : p → r`;
(c) `example : ∃ x : BitVec 4, x + 1#4 = 0#4`.

---

## L8 — How Lean computes: definitional equality

**Idea.** Lean can *unfold and compute* inside types. Two expressions are
**definitionally equal** if computing both gives the same result. Then `rfl`
proves them equal at no cost.

Computation rules (simplified):
- **unfold** a definition (`double 3` → `3 * 2`),
- **apply** a lambda (`(fun x => x + 1) 2` → `2 + 1`),
- **match/recursion** on a constructor (`isZero 0` → `true`),
- **let** substitution.

```lean
example : double 3 = 6 := rfl             -- computes to 6 = 6
example (n : Nat) : n + 0 = n := rfl      -- Nat.add recurses on the 2nd arg: n + 0 ↦ n
example (n : Nat) : 0 + n = n := rfl      -- ✗ FAILS: 0 + n is stuck, n is unknown
example (n : Nat) : 0 + n = n := by omega -- needs real reasoning (or Nat.zero_add)
```

The third example is the single most instructive failure in Lean: `n + 0`
reduces because the definition of `+` pattern-matches on its **second**
argument, which is the constructor `0`. `0 + n` can't reduce because `n` is a
variable — computation is *stuck*, and you need a proof (by induction, or a
library lemma).

**Hardware picture.** Definitional equality is **constant propagation**:
whatever the synthesizer could fold away with the inputs you have is "free".
Anything depending on an unknown input needs a real argument.

**Traps.** Big definitions can make `rfl`/`decide` very slow (they compute
everything). Mark heavy definitions `@[irreducible]` and prove lemmas about
them instead — this matters with large generated RTL models.

**Drill L8.** Predict, then check: (a) `example : sumTo 3 = 6 := rfl`;
(b) `example (b : Bool) : (if b then 1 else 1) = 1 := rfl`;
(c) `example (x : BitVec 8) : x + 0#8 = x := rfl`.

---

## L9 — Tactic mode: goals and the core tactics

**Idea.** Writing proof terms by hand gets painful. **Tactics** are commands
that build the term for you, step by step. After `by`, the infoview shows the
**proof state**:

```
p q : Prop          ← things you have (hypotheses / context)
hp : p
hq : q
⊢ q ∧ p             ← the goal: what you must prove
```

Each tactic transforms the goal(s) until none remain.

```lean
example (p q : Prop) (hp : p) (hq : q) : q ∧ p := by
  constructor        -- splits into two goals: ⊢ q   and   ⊢ p
  · exact hq         -- `·` focuses the first goal
  · exact hp
```

### The core ten

| Tactic | Does | Use when the goal / context looks like |
|---|---|---|
| `intro h` | moves an assumption into the context | goal `p → q` or `∀ x, …` |
| `exact e` | closes the goal with term `e` | you have exactly the evidence |
| `apply f` | uses `f : a → b` backwards; new goal `a` | goal `b` and you have a lemma ending in `b` |
| `constructor` | splits `∧`, `↔`, structures | goal `p ∧ q`, `p ↔ q` |
| `cases h` / `obtain ⟨a, b⟩ := h` | takes evidence apart | `h : p ∧ q`, `h : p ∨ q`, `h : ∃ x, …` |
| `have h : p := …` | proves a helper fact inline | a lemma you need in the middle |
| `show p` | restates the goal (must be defeq) | clarity, or to unfold |
| `rfl` | closes `a = a` (up to computation) | both sides compute the same |
| `simp` | simplifies with a lemma database | algebraic clean-up |
| `omega` | solves linear arithmetic over `Nat`/`Int` | `+`, `-`, `*` by constants, `<`, `≤`, `%` by constants |

```lean
example (p q r : Prop) : (p → q) → (q → r) → p → r := by
  intro hpq hqr hp
  apply hqr          -- goal becomes ⊢ q
  apply hpq          -- goal becomes ⊢ p
  exact hp

example (x y : Nat) (h : x < y) : x + 1 ≤ y := by
  omega
```

### Structure and combinators
- `·` focuses one goal (indentation matters).
- `t1 <;> t2` runs `t2` on every goal produced by `t1`.
- `all_goals t`, `any_goals t`, `first | t1 | t2`, `repeat t`, `try t`.
- `next => …` names an anonymous case.
- `sorry` leaves a hole (Lean warns; `#print axioms` shows `sorryAx`).

**Hardware picture.** The goal list is your **proof grid**: each open goal is
an obligation still "undetermined". Tactics are the engine invocations — except
*you* choose which engine and in what order.

**Traps.**
- After every tactic, **look at the infoview**. Fluency is mostly the habit of
  reading the goal before typing.
- `exact` needs the *exact* type, up to computation. If it doesn't fit, try
  `apply` (which tolerates missing arguments) or `simpa using e`.

**Drill L9.** (a) `example (p q : Prop) : p ∧ q → q ∧ p := by …`
(b) `example (a b : Nat) (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by …`
(c) Use `have` to prove `example (n : Nat) (h : n > 5) : n * 2 > 10 := by …`

---

## L10 — Equality and rewriting: `rw`, `simp`

### `rw` — replace one side of an equation with the other

```lean
example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1]          -- goal: b = c
  exact h2         -- (rw would also close it: rw [h1, h2])

example (a b : Nat) : a + b = b + a := by
  rw [Nat.add_comm]
```

- `rw [h]` rewrites left-to-right; `rw [← h]` right-to-left.
- `rw [h] at h2` rewrites inside a hypothesis.
- `rw` closes the goal automatically if it becomes `x = x`.

### `simp` — the workhorse

`simp` repeatedly rewrites with every lemma tagged `@[simp]` (thousands in
core) plus what you give it:

```lean
example (xs : List Nat) : (xs ++ []).length = xs.length := by simp
example (x : BitVec 8) : x &&& x = x := by simp

def step (s : Nat) (en : Bool) : Nat := if en then s + 1 else s

example (s : Nat) : step s false = s := by simp [step]   -- unfold `step`, then simplify
```

| Form | Meaning |
|---|---|
| `simp` | default simp set |
| `simp [foo, h]` | also unfold `foo` / rewrite with `h` |
| `simp only [foo, h]` | *only* these — predictable, preferred in finished proofs |
| `simp at h` | simplify a hypothesis |
| `simp at *` | everywhere |
| `simpa using h` | simplify goal *and* `h`, then close with `h` |
| `simp?` | runs `simp` and **tells you** the `simp only [...]` call it used |

**Hardware picture.** `simp` is logic optimisation with a rule database;
`simp only` is running a specific pass.

**Traps.**
- "`rw` failed: did not find instance of the pattern" — the left-hand side
  doesn't appear *syntactically* (maybe hidden behind a definition: `unfold` it
  first, or use `simp`).
- `simp` can loop if you give it `h : a = b` and `h' : b = a`.
- Bare `simp` in the middle of a long proof is fragile across Lean versions;
  replace it with the output of `simp?` once it works.

**Drill L10.** (a) Prove `example (a b : Nat) (h : a = 2 * b) : a + a = 4 * b`
two ways (`rw` then `omega`; just `omega`). (b) Use `simp?` on
`example (xs : List Nat) : (xs.map id).length = xs.length := by simp` and paste
its suggestion.

---

## L11 — Logic tactics: cases, existentials, contradiction

```lean
-- Using an Or: two cases
example (p q : Prop) (h : p ∨ q) : q ∨ p := by
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

-- Proving an Or: pick a side
example (n : Nat) : n = 0 ∨ n > 0 := by
  cases n with
  | zero   => left; rfl
  | succ m => right; omega

-- Using an Exists: unpack witness and proof
example (h : ∃ n : Nat, n > 5) : ∃ m : Nat, m > 4 := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by omega⟩

-- Proving an Exists: give a witness
example : ∃ x : BitVec 8, x * 2#8 = 0#8 ∧ x ≠ 0#8 := by
  exact ⟨128#8, by decide⟩

-- Case split on any decidable proposition
example (x : Nat) : x % 2 = 0 ∨ x % 2 = 1 := by
  by_cases h : x % 2 = 0
  · left; exact h
  · right; omega

-- Splitting on an `if` inside the goal
example (c : Bool) (a : Nat) : (if c then a else a) = a := by
  split <;> rfl

-- Contradiction
example (p : Prop) (hp : p) (hnp : ¬ p) : 1 = 2 := by
  exact absurd hp hnp        -- or: contradiction
```

| Have / want | Tactic |
|---|---|
| want `p ∨ q` | `left` / `right` |
| have `h : p ∨ q` | `cases h` / `rcases h with hp | hq` |
| want `∃ x, P x` | `exact ⟨w, proof⟩` / `refine ⟨w, ?_⟩` / `exists w` |
| have `h : ∃ x, P x` | `obtain ⟨x, hx⟩ := h` |
| want `¬ p` | `intro hp` (then prove `False`) |
| have contradictory facts | `contradiction`, `absurd`, `omega`, `simp_all` |
| want anything, have `h : False` | `exact h.elim` / `contradiction` |
| want `p ↔ q` | `constructor` then two implications |
| an `if` / `match` in the goal | `split` |
| a Bool variable `b` | `cases b` (two cases: `false`, `true`) |

**Hardware picture.** `cases b` on a Bool input is case-splitting on an input
bit — exactly what a SAT engine does internally, but here you choose where.

**Drill L11.** (a) `example (p q : Prop) : p ∧ q ↔ q ∧ p`;
(b) `example (f : Nat → Nat) (h : ∀ x, f x > x) : ∃ y, y > 3 := …` (hint:
`f 3`); (c) `example (b : Bool) : (b && !b) = false := by cases b <;> rfl`.

---

## L12 — Induction

**Idea.** To prove `P n` for **all** `n : Nat`, prove `P 0` (base) and
"`P n` implies `P (n+1)`" (step). That's it — and it's exactly the shape of a
proof about all clock cycles.

```lean
theorem zero_add' (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl                       -- 0 + 0 = 0 computes
  | succ k ih =>                      -- ih : 0 + k = k   goal: 0 + (k + 1) = k + 1
    rw [← Nat.add_assoc, ih]          -- 0 + (k+1) → (0+k)+1 → k+1

def dbl : Nat → Nat
  | 0     => 0
  | n + 1 => dbl n + 2

theorem dbl_eq (n : Nat) : dbl n = 2 * n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [dbl]                   -- goal: dbl k + 2 = 2 * (k + 1)
    omega                             -- linear, using ih : dbl k = 2 * k

theorem sumTo_ge (n : Nat) : sumTo n ≥ n := by
  induction n with
  | zero => decide
  | succ k ih => simp only [sumTo]; omega
```

Notice the rhythm: **unfold one step of the definition, then use the IH**.
When the leftover algebra is non-linear (e.g. proving
`2 * sumTo n = n * (n + 1)`, which has `k * k` in it), `omega` can't finish;
you either do the algebra by hand with rewrite lemmas, or reach for `grind`
(core) / `ring` (Mathlib) — see L13.

### Induction on other types

Every `inductive` type gets an induction principle:

```lean
theorem length_append (xs ys : List Nat) :
    (xs ++ ys).length = xs.length + ys.length := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.cons_append, List.length_cons, ih]
    omega
```

### `generalizing` — the most important induction skill

If the statement has *other* variables that change during the recursion, you
must let the induction hypothesis quantify over them:

```lean
def runFrom (step : Nat → Nat) : Nat → Nat → Nat   -- start state, cycles
  | s, 0     => s
  | s, n + 1 => runFrom step (step s) n

theorem runFrom_inv (step : Nat → Nat) (Inv : Nat → Prop)
    (hstep : ∀ s, Inv s → Inv (step s)) :
    ∀ n s, Inv s → Inv (runFrom step s n) := by
  intro n
  induction n with
  | zero => intro s hs; exact hs
  | succ k ih =>
    intro s hs
    exact ih (step s) (hstep s hs)      -- IH used at a *different* start state
```

Here we kept `s` universally quantified in the statement (`∀ n s`) and only
introduced `n` before `induction`, so the IH is about **every** start state.
Writing `intro n s hs; induction n` instead gives an IH about one fixed `s` —
and the proof gets stuck. `induction n generalizing s` does the same fix for
you.

**Hardware picture.** This is the difference between
"the property holds along *this* trace" and "the property is preserved from
*any* state satisfying the invariant" — i.e. it's the **induction step from an
arbitrary state** that k-induction checks. A stuck `generalizing`-less proof is
the Lean version of an induction counterexample.

**Traps.**
- Stuck in the step case? Check whether your IH talks about the right
  state/argument. Nine times out of ten you need `generalizing`.
- Prove the **strongest** statement you can; weak statements make weak IHs.

**Drill L12.** (a) Prove `∀ n, pow2 n > 0` (from Drill L2), using the
"unfold one step, then `omega`" rhythm. (b) Prove
`(xs.map f).length = xs.length` by induction on `xs`. (c) Prove
`runFrom step s (a + b) = runFrom step (runFrom step s a) b` — which variable
must be generalized?

---

## L13 — Decision procedures: `decide`, `omega`, `bv_decide`, `grind`

**Idea.** For some classes of goals, a tactic can find the proof by itself.
Each has a different power, speed, and **trust** cost.

| Tactic | Works on | How | Trust |
|---|---|---|---|
| `rfl` | equalities that compute | kernel evaluation | kernel only |
| `decide` | closed, finite, decidable props (small!) | kernel evaluates the `Decidable` instance | kernel only |
| `native_decide` | same, bigger | compiles and runs native code | + compiler (`Lean.ofReduceBool`) |
| `omega` | linear arithmetic over `Nat`/`Int` (`+`, `-`, constant `*`, `/`/`%` by constants, `<`, `≤`, `=`, `∧∨¬`) | Presburger decision procedure, produces a kernel proof | kernel only |
| `simp` / `simp_all` | rewriting to `True` | lemma database | kernel only |
| `bv_decide` | `BitVec`/`Bool` goals: arithmetic, bitwise, shifts, comparisons, `if` | **bit-blast to SAT, run CaDiCaL, check LRAT certificate** with a verified checker | + `Lean.ofReduceBool` |
| `grind` | mixed reasoning: congruence closure, arithmetic, case splits, E-matching on lemmas | SMT-solver-style search inside Lean, kernel-checked | kernel only |

```lean
example : (255#8) + 1#8 = 0#8 := by decide
example (x y : Nat) (h : x + 2 ≤ y) : x < y := by omega

-- 32-bit facts: too big for `decide`, perfect for `bv_decide`
example (x : BitVec 32) : x + x = x <<< 1 := by bv_decide
example (x y : BitVec 32) : (x ^^^ y) ^^^ y = x := by bv_decide
example (a b : BitVec 32) : a - b = a + (~~~b + 1#32) := by bv_decide

theorem xor_cancel (x y : BitVec 32) : (x ^^^ y) ^^^ y = x := by bv_decide
#print axioms xor_cancel   -- lists Lean.ofReduceBool: the SAT certificate check ran as compiled code
```

When `bv_decide` fails it gives a **counterexample** — values for the
variables, just like a CEX trace:

```lean
example (x : BitVec 8) : x + 1#8 > x := by bv_decide
-- fails: counterexample x = 255 (wrap-around)
```

**Choosing:**
1. Arithmetic over `Nat`/`Int` → `omega`.
2. Fixed-width bit-vector fact → `bv_decide`.
3. "Obvious" algebra/plumbing → `simp`, then `grind`.
4. Tiny finite check → `decide`.
5. Needs induction or a creative invariant → **you** (L12), then the above for the leaves.

**Hardware picture.** This is your engine portfolio: `bv_decide` is the SAT
engine, `omega` an arithmetic engine, `decide` exhaustive simulation. The
difference: **you** decide which sub-goal goes to which engine, and the result
is a checked proof, not a verdict. (Course Part B6 explains the
SAT-in-a-prover design.)

**Traps.**
- `decide` refuses goals that mention local variables (it reports that the
  goal contains free variables) and gets stuck on anything it cannot fully
  evaluate. First make the goal closed (e.g. `show 0#4 ≤ 9#4`). On large
  finite domains it's impractically slow — use `bv_decide`.
- `omega` doesn't do non-linear arithmetic (`x * y` with both variables). It
  treats `x * y` as an opaque atom.
- `bv_decide` needs the goal to be about `BitVec`/`Bool`. Unfold your
  definitions first (`simp only [myDef]` or `unfold myDef`).

**Drill L13.** Choose and apply the right tactic: (a) `∀ x : BitVec 16, x &&& 0#16 = 0#16`;
(b) `(n : Nat) (h : n % 4 = 3) : n % 2 = 1`;
(c) `(x : BitVec 8) : x.slt 0#8 = x.getLsbD 7` (hint: msb);
(d) find the counterexample: `(x : BitVec 8) : x * 3#8 ≠ 1#8`.

---

## L14 — Modelling a circuit end to end

A BCD-style counter: counts 0…9 when `en` is high, then wraps to 0.

```systemverilog
always_ff @(posedge clk)
  if (rst)     cnt <= 4'd0;
  else if (en) cnt <= (cnt == 4'd9) ? 4'd0 : cnt + 4'd1;

assert property (@(posedge clk) cnt <= 4'd9);
```

### 1. The model

```lean
namespace Bcd

/-- Next-state function: the `always_ff` body. -/
def next (cnt : BitVec 4) (en : Bool) : BitVec 4 :=
  if en then (if cnt = 9#4 then 0#4 else cnt + 1#4) else cnt

/-- State after `n` cycles, from reset, for input stream `ins`. -/
def run (ins : Nat → Bool) : Nat → BitVec 4
  | 0     => 0#4
  | n + 1 => next (run ins n) (ins n)

#eval run (fun _ => true) 12      -- 2   (0,1,…,9,0,1,2)
```

`ins : Nat → Bool` is "the value of input `en` at every cycle" — an arbitrary
input stream, like a free input in Jasper.

### 2. The property

```lean
/-- The assertion: holds at every cycle, for every input stream. -/
theorem cnt_le_9 (ins : Nat → Bool) (n : Nat) : run ins n ≤ 9#4 := by
  induction n with
  | zero =>
    show 0#4 ≤ 9#4                      -- run ins 0 computes to 0#4 (definitional)
    decide                              -- closed goal: evaluate it
  | succ k ih =>
    show next (run ins k) (ins k) ≤ 9#4 -- unfold one step (definitional)
    exact next_le_9 _ _ ih              -- the step lemma below
```

### 3. The step lemma (the inductive step, delegated to SAT)

```lean
theorem next_le_9 (c : BitVec 4) (en : Bool) (h : c ≤ 9#4) : next c en ≤ 9#4 := by
  unfold next
  bv_decide
```

(Put `next_le_9` *before* `cnt_le_9` in the file — Lean reads top to bottom.)

### What just happened, in Jasper terms

| Lean | Jasper |
|---|---|
| `next` | the RTL's next-state logic |
| `run ins n` | the state at cycle `n` under arbitrary inputs |
| `zero` case | the base case of induction (reset state satisfies the property) |
| `next_le_9` | the induction step: *from any state* satisfying the property, one step preserves it |
| `bv_decide` in the step | a SAT call on one transition — exactly what an induction engine does |
| No bound anywhere | the result holds for all `n` — a full proof, not a bounded one |

The property happened to be **inductive** on its own. If it weren't (e.g. a
one-hot FSM where a non-reachable state violates the step), `bv_decide` in
`next_le_9` would return a **counterexample state** — your induction CEX — and
you'd strengthen the invariant (Part D3).

**Drill L14.** (a) Prove `run ins n ≠ 10#4`. (b) Change the RTL bug-style:
wrap at `cnt == 10`. Which proof breaks, and what counterexample do you get?
(c) Prove the property "if `en` is low, the counter holds its value":
`ins n = false → run ins (n+1) = run ins n`.

---

## L15 — Organising proofs

```lean
namespace Bcd

-- equations about `run`, tagged so `simp` uses them automatically
@[simp] theorem run_zero (ins : Nat → Bool) : run ins 0 = 0#4 := rfl
@[simp] theorem run_succ (ins : Nat → Bool) (n : Nat) :
    run ins (n + 1) = next (run ins n) (ins n) := rfl

section
variable (ins : Nat → Bool)      -- shared argument for every lemma in this section

private theorem le9 (n : Nat) : run ins n ≤ 9#4 := cnt_le_9 ins n   -- file-local

theorem ne_15 (n : Nat) : run ins n ≠ 15#4 := by
  have h := le9 ins n
  bv_decide
end

end Bcd
```

- **Small lemmas, then compose.** Each lemma should be one idea. This is the
  same discipline as helper assertions, and it's what makes the Ibex proof
  converge (course D10).
- **Name lemmas by their statement**: `next_le_9`, `run_succ`,
  `count_le_depth`. (Mathlib convention: describe the conclusion,
  `_of_` for hypotheses, e.g. `le_of_lt`.)
- **`@[simp]` lemmas** that rewrite "complicated → simpler" (never the reverse)
  build your own simp set.
- **`open Foo`** to use short names; `open Foo in` for one declaration only.
- **`section … end`** + `variable` to share hypotheses across lemmas.
- **`example`** for scratch work; **`theorem`** for things you'll reuse.
- Keep **`sorry` visible**: CI forbids it in solutions (`#print axioms` check).

---

## L16 — Reading errors and getting unstuck

### The error messages you'll see most

| Message | Usually means | Try |
|---|---|---|
| `unsolved goals` | proof ended with goals left | look at the listed goal; add tactics |
| `type mismatch … has type A but is expected to have type B` | evidence doesn't fit | `#check` both; maybe `apply` / `simpa using` / a cast |
| `failed to synthesize instance Decidable …` | used a non-decidable Prop in `if`/`decide` | make it Bool, or `open Classical`, or prove it differently |
| `failed to synthesize instance HAdd …` | adding different types (e.g. `Nat` + `BitVec 8`) | annotate types, convert explicitly |
| `unknown identifier` / `unknown constant` | typo, wrong namespace, or defined later in the file | `open`, full name, reorder |
| `rw failed: did not find instance of pattern` | LHS not literally present | `unfold`, `simp only`, or `show` first |
| `motive is not type correct` | rewriting something a type depends on | use `simp` instead of `rw`, or `subst` |
| `failed to prove termination` | Lean can't see a decreasing measure | `termination_by`, `decreasing_by omega` |
| `maximum recursion depth reached` | huge computation in `decide`/`rfl` | use `bv_decide`/lemmas; `@[irreducible]` |
| `declaration uses 'sorry'` | a hole remains | find it — CI will |
| `omega could not prove the goal` + a counterexample | the arithmetic claim is false *or* has non-linear parts | read the counterexample; check for `x * y` |

### Search tactics — let Lean find the lemma

| Tactic | Finds |
|---|---|
| `exact?` | a library lemma that closes the goal |
| `apply?` | lemmas whose conclusion matches the goal |
| `rw?` | rewrites that apply |
| `simp?` | the exact `simp only [...]` call |
| `#check @Nat.add_comm` | the statement of a lemma |
| `#print axioms thm` | what a theorem trusts |

### A routine when stuck
1. **Read the goal.** Out loud. What are the types?
2. Is there a definition hiding the structure? `unfold f` / `simp only [f]`.
3. Is it arithmetic? `omega`. Bit-vectors? `bv_decide`. Mixed? `grind`.
4. Is it a case split? `cases`, `split`, `by_cases`.
5. Is it about all cycles / all `n`? `induction` — and check `generalizing`.
6. Is it a false statement? Try a concrete value with `#eval` or let
   `bv_decide`/`omega` find a counterexample.
7. Still stuck: state a **smaller lemma** with `have … := by sorry`, finish the
   main proof, then go back. (Top-down proof, like writing helper assertions first.)
8. Ask the tutor (`ftwin tutor` or the tutor pane): it sees the goal.

---

## L17 — Semantics under the hood (simplified)

You can be fluent without this, but it explains *why* things behave as they do.

### 17.1 Two layers: surface language and kernel
What you type (notation, implicit arguments, tactics, `match`, `do`) is
**elaborated** into a small core language of terms. The **kernel** only checks
core terms. Tactics are programs that *generate* core terms; they are not
trusted — only their output is checked.

```
your text ──parse──► syntax ──elaborate──► core term ──kernel check──► accepted
                      (macros,   (fill implicits, resolve
                       notation)  instances, run tactics,
                                  compile match/recursion)
```

### 17.2 Everything has a type — even types
`5 : Nat`, `Nat : Type`, `Type : Type 1`, … This tower of **universes**
avoids paradoxes. `Prop` sits at the bottom (`Prop : Type`). You'll mostly see
`Type` and `Prop`; `Sort u` is the general form; universe errors in normal
hardware work are rare.

### 17.3 Dependent types
A type can depend on a **value**: `BitVec n` depends on `n`; `Fin 32` on 32.
A function's *output type* can depend on its *input value*:

```lean
def zeros (n : Nat) : BitVec n := 0#n    -- output width = input value
```

And `∀ x, P x` is a dependent function type: the type of the result (`P x`)
depends on the input `x`. That's why `∀` and function arrows are the same
thing in Lean.

### 17.4 Definitional vs. propositional equality
- **Definitional** (`≡`): the kernel sees it by computing (L8). Free. `rfl` works.
- **Propositional** (`=`): needs a proof. E.g. `0 + n = n` is propositionally
  but not definitionally true.

Tactics like `rw` and `simp` *use* propositional equalities to change goals.

### 17.5 Proof irrelevance
Any two proofs of the same `Prop` are considered equal. You never care *which*
proof you have — only that you have one. This is why proofs can be erased
when compiling code, and why `Prop` behaves differently from `Bool`.

### 17.6 Axioms
Core Lean's logic adds three axioms: `propext` (equivalent props are equal),
`Quot.sound` (quotients), and `Classical.choice` (gives the law of excluded
middle). Plus, if you use `native_decide`/`bv_decide`, `Lean.ofReduceBool`
(trust the compiler's evaluation). `#print axioms` lists exactly which a
theorem depends on — the most precise "trust base" report you'll ever get
from a verification tool.

### 17.7 Inductive types generate their rules
Declaring `inductive T` gives Lean: the constructors, a **recursor**
(`T.rec`) that is simultaneously "structural recursion" and "induction", and
the facts that constructors are distinct and injective. `match`, `cases`,
`induction` and structural recursion are all elaborated into uses of `T.rec`.
That's why recursion and induction feel the same: they *are* the same.

---

## Appendix A — Cheat sheets

### Goal shape → first move

| Goal | Try |
|---|---|
| `p → q`, `∀ x, …` | `intro` |
| `p ∧ q`, `p ↔ q` | `constructor` |
| `p ∨ q` | `left` / `right` |
| `∃ x, P x` | `exact ⟨w, _⟩` / `refine ⟨w, ?_⟩` |
| `¬ p` | `intro h` |
| `a = b` (computes) | `rfl` |
| `a = b` (algebra) | `simp`, `omega`, `rw [...]`, `grind` |
| `BitVec` fact | `bv_decide` |
| Contains `if`/`match` | `split` |
| About all `n` / all cycles | `induction n (generalizing …)` |
| `False` | find a contradiction: `contradiction`, `omega`, `simp_all` |

### Hypothesis shape → first move

| Hypothesis | Try |
|---|---|
| `h : p ∧ q` | `obtain ⟨hp, hq⟩ := h` |
| `h : p ∨ q` | `rcases h with hp | hq` |
| `h : ∃ x, P x` | `obtain ⟨x, hx⟩ := h` |
| `h : a = b` | `rw [h]`, `subst h`, `simp [h]` |
| `h : p → q` | `apply h`, `exact h hp`, `have hq := h hp` |
| `h : ∀ x, P x` | `have := h 5`, `specialize h 5` |
| `h : False` | `exact h.elim` |
| `b : Bool` | `cases b` |

### Lean ⇄ RTL/Jasper

| Lean | RTL / Jasper |
|---|---|
| `def f (x : BitVec 8) : BitVec 8` | combinational module |
| `structure` | packed struct |
| `inductive` (no args) | enum |
| `match` (checked complete) | `unique case` that's actually enforced |
| `Nat → I` | free input stream |
| `run c ins n` | state at cycle `n` |
| `theorem … : ∀ ins n, P (run c ins n)` | `assert property (P)` — full proof |
| hypothesis `(h : ∀ n, A (ins n))` | `assume property (A)` |
| `have` / lemma | helper assertion |
| `induction` + step lemma | induction engine with your invariant |
| `bv_decide` | SAT engine call (with checked certificate) |
| `sorry` | undetermined / waived |
| failing step goal | induction CEX |
| `#print axioms` | trust-base report |

## Appendix B — Unicode input (VS Code: type `\` + name)

| Symbol | Type | Symbol | Type |
|---|---|---|---|
| `→` | `\to` | `←` | `\l` |
| `∀` | `\forall` | `∃` | `\exists` |
| `∧` | `\and` | `∨` | `\or` |
| `¬` | `\not` | `↔` | `\iff` |
| `≠` | `\ne` | `≤` `≥` | `\le` `\ge` |
| `⟨ ⟩` | `\<` `\>` | `·` | `\.` |
| `ℕ` | `\N` | `×` | `\x` |
| `⊢` | `\|-` | `↑` | `\u` |

## Appendix C — Drill solutions

**L1.** (a) `Nat → Nat → Nat`. (b) `[11, 21, 31]`. (c) `Nat` subtraction
truncates at 0.

**L2.**
```lean
def pow2 : Nat → Nat
  | 0     => 1
  | n + 1 => 2 * pow2 n

def popcount : List Bool → Nat
  | []          => 0
  | true :: bs  => 1 + popcount bs
  | false :: bs => popcount bs
```
(c) "missing cases" error naming `St.done`.

**L3.**
```lean
structure FifoState where
  rd    : Fin 8
  wr    : Fin 8
  count : Nat

def Instr.dest : Instr → Option (Fin 32)
  | .alu _ rd _ _ => some rd
  | .addi rd _ _  => some rd
  | .halt         => none
```
(b) `isLogic` still compiles (it has a `_` catch-all); any `match` without a
catch-all reports a missing case for `slt`.

**L4.**
```lean
def signBit (x : BitVec 32) : Bool := x.getLsbD 31     -- or x.msb

def immI (instr : BitVec 32) : BitVec 32 :=
  (instr.extractLsb 31 20).signExtend 32
```
(c) `4294967295` (all ones in 32 bits).

**L5.** (b)
```lean
def max3 {α : Type} [Max α] (a b c : α) : α := max a (max b c)
```

**L6.**
```lean
#check ∀ x : BitVec 8, x + 0#8 = x
#check ∃ x : BitVec 4, x ≠ 0#4 ∧ -x = x          -- x = 8
-- (c), with some `count : Nat` and `full : Bool` in scope:
--   count = 8 → full = true
```

**L7.**
```lean
example (p q : Prop) : p → q → p := fun hp _ => hp
example (p q r : Prop) (hpq : p → q) (hqr : q → r) : p → r := fun hp => hqr (hpq hp)
example : ∃ x : BitVec 4, x + 1#4 = 0#4 := ⟨15#4, by decide⟩
```

**L8.** (a) works (`sumTo 3` computes to 6). (b) works only after splitting:
`if b then 1 else 1` is stuck on unknown `b` — use `by cases b <;> rfl`.
(c) likely fails by `rfl` (BitVec addition is defined via `Nat` arithmetic
modulo 2ⁿ, which gets stuck on a variable); use `by simp` or `by bv_decide`.

**L9.**
```lean
example (p q : Prop) : p ∧ q → q ∧ p := by
  intro ⟨hp, hq⟩
  exact ⟨hq, hp⟩

example (a b : Nat) (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by omega

example (n : Nat) (h : n > 5) : n * 2 > 10 := by
  have h2 : n * 2 = n + n := by omega
  omega
```

**L10.**
```lean
example (a b : Nat) (h : a = 2 * b) : a + a = 4 * b := by rw [h]; omega
example (a b : Nat) (h : a = 2 * b) : a + a = 4 * b := by omega
```

**L11.**
```lean
example (p q : Prop) : p ∧ q ↔ q ∧ p := by
  constructor
  · intro ⟨hp, hq⟩; exact ⟨hq, hp⟩
  · intro ⟨hq, hp⟩; exact ⟨hp, hq⟩

example (f : Nat → Nat) (h : ∀ x, f x > x) : ∃ y, y > 3 :=
  ⟨f 3, h 3⟩

example (b : Bool) : (b && !b) = false := by cases b <;> rfl
```

**L12.**
```lean
theorem pow2_pos (n : Nat) : pow2 n > 0 := by
  induction n with
  | zero => decide
  | succ k ih => simp only [pow2]; omega

theorem map_length (f : Nat → Nat) (xs : List Nat) :
    (xs.map f).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x rest ih => simp [ih]

theorem runFrom_add (step : Nat → Nat) (a b : Nat) :
    ∀ s, runFrom step s (a + b) = runFrom step (runFrom step s a) b := by
  induction a with
  | zero => intro s; simp [runFrom]
  | succ k ih =>
    intro s
    rw [Nat.add_right_comm]
    simp only [runFrom]
    exact ih (step s)
```
(The start state `s` must be generalized — it changes on every step.)

**L13.**
```lean
example : ∀ x : BitVec 16, x &&& 0#16 = 0#16 := by intro x; bv_decide
example (n : Nat) (h : n % 4 = 3) : n % 2 = 1 := by omega
example (x : BitVec 8) : x.slt 0#8 = x.getLsbD 7 := by bv_decide
example (x : BitVec 8) : x * 3#8 ≠ 1#8 := by bv_decide
-- fails with counterexample x = 171 (3 * 171 = 513 = 2*256 + 1)
```

**L14.**
```lean
theorem cnt_ne_10 (ins : Nat → Bool) (n : Nat) : run ins n ≠ 10#4 := by
  have h := cnt_le_9 ins n
  bv_decide        -- from c ≤ 9 conclude c ≠ 10 (treats `run ins n` as an atom)

theorem hold (ins : Nat → Bool) (n : Nat) (h : ins n = false) :
    run ins (n + 1) = run ins n := by
  show next (run ins n) (ins n) = run ins n
  rw [h]
  simp [next]
```
(b) Wrapping at 10 lets `cnt` reach 10: `cnt_le_9`'s step lemma fails;
`bv_decide` reports `c = 9, en = true` (9 + 1 = 10 > 9).
