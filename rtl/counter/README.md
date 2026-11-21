# counter — BCD counter (twin lab D1/D2, Lean fluency L14)

Counts 0…9 while `en` is high, then wraps to 0. The same design appears in three places:

| Where | What |
|---|---|
| `rtl/counter/counter.sv` | RTL plus formal properties (this directory) |
| `docs/LEAN_FLUENCY.md` L14 | Lean model `Bcd.next`/`Bcd.run`, with `cnt_le_9` proven by induction |
| `satlab gen counter-bmc` | The same circuit unrolled to CNF for the SAT lab |

## Properties

| Label | Meaning | Jasper equivalent |
|---|---|---|
| `p_le_9` | `cnt` never exceeds 9 | `assert property (@(posedge clk) disable iff (rst) cnt <= 9);` |
| `p_hold` | `cnt` holds when `en` is low | `assert property (@(posedge clk) disable iff (rst) !en \|=> $stable(cnt));` |
| `c_reach_9` | 9 is reachable | `cover property (@(posedge clk) cnt == 9);` |

Reset handling: the first cycle is assumed to be in reset (`assume (rst)` while
`!f_past_valid`). That corresponds to Jasper's `reset rst` before `prove`.

## Running

With the OSS CAD Suite on `PATH`:

```sh
cd rtl/counter
sby -f counter.sby            # all tasks
sby -f counter.sby bug        # just the injected bug
```

With the pip-installable WebAssembly build (`pip install yowasp-yosys z3-solver`),
which provides everything except ABC (so not the `pdr` task):

```sh
yowasp-sby -f --yosys yowasp-yosys --smtbmc yowasp-yosys-smtbmc \
  --witness yowasp-yosys-witness counter.sby bmc prove cover bug
```

Run the yowasp tasks one or two at a time. Several WebAssembly Yosys processes
running in parallel crashed with SIGBUS in testing.

## Observed results (yowasp-yosys + Z3)

| Task | Engine | Result |
|---|---|---|
| `bmc` | smtbmc z3, depth 20 | PASS |
| `prove` | smtbmc z3, k-induction (depth 4) | PASS: "successful proof by k-induction" |
| `cover` | smtbmc z3 | `c_reach_9` reached at step 10 |
| `bug` (WRAP=10) | smtbmc z3 | FAIL as expected: `p_le_9` violated; VCD trace written |
| `pdr` | abc pdr | needs the OSS CAD Suite (`yosys-abc`) |

## The Lean side

`RtlProof/Generated/Counter.lean` is generated from `counter.sv` by `sv2lean`.
`RtlProof/Examples/Counter/Solution.lean` proves `p_le_9` and `p_hold` on that
model, for every cycle and every input sequence, under the same reset
assumption. Each proof is an inductive invariant (the Lean counterpart of a
helper assertion), with every obligation discharged by `bv_decide`.
`Exercise.lean` is the same file with the proofs removed.

Run both sides together:

```sh
ftwin run counter
```

```
property   side  task/engine               verdict    depth  trusts / evidence
p_le_9     MC    bmc: smtbmc z3            bounded    20     engine
p_le_9     MC    bug: smtbmc z3            cex        11     CEX trace.vcd (expected)
p_le_9     MC    prove: smtbmc z3          proven     4      engine
p_le_9     Lean  Gen.Counter.p_le_9_holds  proved     ∞      kernel + bv_decide (native)
```

Run the same Lean proof against the buggy design (`sv2lean ... -P WRAP=10`)
and the inductive step fails. `bv_decide` reports the induction counterexample
`f_past_valid = 1, cnt = 9, rst = 0, en = 1`: a single transition, not a
11-cycle trace from reset. It labels it "potentially spurious", for the same
reason a Jasper induction counterexample may be unreachable. Here it is real.
