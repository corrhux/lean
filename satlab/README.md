# satlab: the SAT laboratory (course Part B)

Teaching SAT solvers you can read and switch apart, the same instances run
through industrial solvers, and UNSAT proofs you can check.

```sh
pip install -e ".[dev]"       # from the repo root
satlab --help
```

| Command | What it does | Course chapter |
|---|---|---|
| `satlab gen …` | pigeonhole, random k-SAT, add/mul commutativity miters, counter BMC | B1, B4 |
| `satlab solve f.cnf --trace t.jsonl` | teaching CDCL (or `--solver dpll`), with an event trace | B2 |
| `satlab trace t.jsonl --names f.cnf` | step-by-step listing: decide, imply, conflict, learn, backjump | B2 |
| `satlab ablate f.cnf` | CDCL with each technique switched off in turn | B2, B3 |
| `satlab zoo f.cnf` | MiniSat, Glucose, Maple, Lingeling, CaDiCaL, Kissat, Z3 and the teaching solvers on the same CNF | B3 |
| `satlab solve f.cnf --proof p.drup` and `satlab check f.cnf p.drup` | write and check an UNSAT certificate | B5 |

## Lab 1: watch CDCL learn (B2)

```sh
satlab gen pigeonhole -n 2 -o php2.cnf
satlab solve php2.cnf --trace php2.jsonl
satlab trace php2.jsonl --names php2.cnf
```

## Lab 2: a counterexample from a SAT model (B4)

```sh
satlab gen counter-bmc --depth 12 --wrap 10 -o bug.cnf   # off-by-one counter
satlab solve bug.cnf --model
```

The model decodes to the trace `cnt = 0,0,0,1,…,9,10`: the same failure
SymbiYosys reports for `rtl/counter` task `bug`. With `--wrap 9` the instance
is UNSAT: no violation within 12 cycles, which is a bounded result.

## Lab 3: why multipliers are hard for SAT (B3, D6)

`x*y = y*x` encoded as a miter (UNSAT means the two products are equal).
Teaching-CDCL conflicts measured while building this lab:

| width | conflicts |
|---|---|
| 4 | 139 |
| 6 | 2,992 |
| 8 | 54,756 |

Solver zoo at **width 10**, 20 s timeout (4-core cloud VM; times vary by machine):

| solver | result | time |
|---|---|---|
| minisat22, glucose4, maplechrono, lingeling, z3, teaching CDCL/DPLL | TIMEOUT | > 20 s |
| cadical195 | UNSAT | 19.3 s (564k conflicts) |
| kissat404 | UNSAT | 16.8 s |

Compare with Lean, where commutativity of multiplication holds for **every**
width by a library lemma (`BitVec.mul_comm`), with no search at all.

## Lab 4: no heuristic wins everywhere (B3)

`satlab ablate` on the width-6 multiplier miter:

| configuration | conflicts |
|---|---|
| full CDCL | 2,992 |
| no VSIDS (fixed order) | 1,156 |
| no restarts | 2,165 |
| no learned-clause minimisation | 3,082 (and 61k learned literals vs 41k) |

Here fixed-order branching *beats* VSIDS. On random 3-SAT near the threshold
(`satlab gen random -n 150 -m 640 --seed S`) the opposite happens:

| seed | result | full CDCL | no VSIDS |
|---|---|---|---|
| 0 | UNSAT | 2,879 | 27,624 |
| 1 | SAT | 224 | 13,097 |
| 2 | SAT | 3,151 | 10,442 |

The circuit's structure (a variable order that follows the partial-product
array) helps fixed ordering on the miter; random formulas have no structure to
exploit. This is why industrial tools run portfolios of engines.

## Lab 5: checking an UNSAT answer (B5)

```sh
satlab gen mul-miter --width 4 -o m4.cnf
satlab solve m4.cnf --proof m4.drup
satlab check m4.cnf m4.drup          # OK: empty clause derived: UNSAT verified
```

The checker re-derives every learned clause by reverse unit propagation. It
is the same idea as the LRAT check that Lean's `bv_decide` runs inside the
prover, minus the hints that make LRAT fast. The DRUP file is also accepted
by `drat-trim`.
