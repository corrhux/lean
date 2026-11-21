"""Differential testing: Lean model vs. Yosys semantics (ARCHITECTURE §4.2, ADR-6).

For each random seed: pick random initial register values and random inputs for
every cycle. Then

* Yosys: `sat -seq N` with every input and every initial value fixed. This is
  a simulation using the same formal model SymbiYosys checks. Assert, assume
  and cover cells are deleted first; `sat` would otherwise constrain the run.
* Lean: `#eval` the generated `step` function over the same inputs.

Every register must match at every cycle.
"""

from __future__ import annotations

import json
import os
import random
import re
import subprocess
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional

from .frontend import run_yosys, scratch_dir
from .ir import Design

REPO = Path(__file__).resolve().parents[2]


@dataclass
class Result:
    seeds: int
    cycles: int
    mismatches: List[str] = field(default_factory=list)
    unknown_outputs: int = 0
    compared_outputs: int = 0

    @property
    def ok(self) -> bool:
        return not self.mismatches

    def summary(self) -> str:
        if self.ok:
            extra = f" ({self.unknown_outputs} x-valued output samples skipped)" if self.unknown_outputs else ""
            return (f"difftest OK: {self.seeds} random runs x {self.cycles} cycles, "
                    f"all registers and outputs match Yosys{extra}")
        return "difftest FAILED:\n  " + "\n  ".join(self.mismatches[:20])


def _wave_values(sig: dict, width: int, steps: int) -> List[Optional[int]]:
    """Decode one WaveJSON signal; position k = time step k (position 0 unused)."""
    wave, data = sig["wave"], sig.get("data", [])
    out: List[Optional[int]] = []
    cur: Optional[int] = None
    di = 0
    for ch in wave:
        if ch == ".":
            pass
        elif ch in "01" and width == 1 and not data:
            cur = int(ch)
        elif ch in "=23456789" and data:
            # WaveDrom: '=' and the digit "colour" characters all take the next data entry;
            # Yosys writes x values as '4' with an empty entry.
            s = data[di] if di < len(data) else ""
            di += 1
            cur = int(s, 2) if s and set(s) <= {"0", "1"} else None
        else:
            cur = None
        out.append(cur)
    # Designs with registers get a leading placeholder position; purely combinational
    # designs do not. The last `steps` positions are the time steps in both cases.
    return out[-steps:] if len(out) >= steps else out + [None] * (steps - len(out))


def _yosys_trace(netlist_path: str, design: Design, init: Dict[str, int],
                 inputs: List[Dict[str, int]]) -> Dict[str, List[Optional[int]]]:
    n = len(inputs)
    args = [f"sat -seq {n}"]
    for r in design.regs:
        how = "-set" if r.free else "-set-init"      # $anyconst: same value at every step
        args.append(f"{how} {r.sig.yosys_name} {r.sig.width}'d{init[r.sig.name]}")
    for t, vec in enumerate(inputs, 1):
        for s in design.inputs:
            if not s.undef:        # x constants: zeroed in Yosys below, set to 0 in Lean
                args.append(f"-set-at {t} {s.yosys_name} {s.width}'d{vec[s.name]}")
    for r in design.regs:
        args.append(f"-show {r.sig.yosys_name}")
    for name, _ in design.outputs:
        args.append(f"-show {name}")
    with tempfile.TemporaryDirectory(dir=scratch_dir()) as td:
        wj = os.path.join(td, "wave.json")
        args.append(f"-dump_json {wj}")
        run_yosys(f"read_json {netlist_path}; delete t:$assert t:$assume t:$cover; setundef -zero; "
                  + " ".join(args))
        raw = Path(wj).read_text()
        # Yosys writes names such as `$memory\mem[0]` without escaping the backslash.
        raw = re.sub(r'\\(?![\\"/bfnrtu])', r'\\\\', raw)
        waves = json.loads(raw)["signal"]
    by_name = {w["name"].lstrip("\\"): w for w in waves}
    out = {}
    for r in design.regs:
        key = r.sig.yosys_name.lstrip("\\")
        out[r.sig.name] = _wave_values(by_name[key], r.sig.width, n) if key in by_name else [None] * n
    for name, bits in design.outputs:
        out["out:" + name] = (_wave_values(by_name[name], len(bits), n) if name in by_name
                              else [None] * n)
    return out


def _lean_trace(model: str, ns: str, design: Design, init: Dict[str, int],
                inputs: List[Dict[str, int]]) -> Dict[str, List[int]]:
    def rec(fields: Dict[str, str]) -> str:
        return "{ " + ", ".join(f"{k} := {v}" for k, v in fields.items()) + " }" if fields else "{}"

    ins = [rec({s.name: f"{vec[s.name]}#{s.width}" for s in design.inputs}) for vec in inputs]
    s0 = rec({r.sig.name: f"{init[r.sig.name]}#{r.sig.width}" for r in design.regs})
    from .emit_lean import Ctx, bits_expr
    cols = [f"s.{r.sig.name}.toNat" for r in design.regs]
    cols += [f"({bits_expr(design, bits, Ctx('w.'))}).toNat" for _, bits in design.outputs]
    harness = f"""
namespace {ns}
def dtInputs : List Input := [{", ".join(ins)}]
/-- (state, input) at every cycle -/
def dtPairs : List (State × Input) :=
  (dtInputs.foldl (fun (acc : List (State × Input) × State) i => (acc.1 ++ [(acc.2, i)], step acc.2 i))
    ([], {s0})).1
#eval IO.println (toString (dtPairs.map fun (s, i) => let w := comb s i; ([{", ".join(cols)}] : List Nat)))
end {ns}
"""
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False, dir=REPO / "build") as f:
        f.write(model + harness)
        path = f.name
    try:
        lake = os.environ.get("LAKE", "lake")
        p = subprocess.run([lake, "env", "lean", path], cwd=REPO, capture_output=True, text=True)
    finally:
        os.unlink(path)
    if p.returncode != 0:
        raise RuntimeError(f"Lean failed on the generated model:\n{p.stdout}\n{p.stderr}")
    line = [l for l in p.stdout.splitlines() if l.startswith("[")][-1]
    rows = json.loads(line)
    names = [r.sig.name for r in design.regs] + ["out:" + n for n, _ in design.outputs]
    return {name: [row[k] for row in rows] for k, name in enumerate(names)}


def run(doc: dict, design: Design, model: str, ns: str, seeds: int = 10, cycles: int = 30) -> Result:
    for r in design.regs:
        if not r.sig.yosys_name:
            raise RuntimeError(f"register {r.sig.name} has no Yosys net name; cannot difftest")
    (REPO / "build").mkdir(exist_ok=True)
    res = Result(seeds, cycles)
    with tempfile.TemporaryDirectory(dir=scratch_dir()) as td:
        npath = os.path.join(td, "netlist.json")
        json.dump(doc, open(npath, "w"))
        for seed in range(seeds):
            rng = random.Random(seed)
            init = {r.sig.name: rng.getrandbits(r.sig.width) for r in design.regs}
            inputs = [{s.name: 0 if s.undef else rng.getrandbits(s.width) for s in design.inputs}
                      for _ in range(cycles)]
            ys = _yosys_trace(npath, design, init, inputs)
            ln = _lean_trace(model, ns, design, init, inputs)
            keys = [r.sig.name for r in design.regs if not r.free]   # $anyconst: pinned, not dumped
            keys += ["out:" + n for n, _ in design.outputs]
            for key in keys:
                for t in range(cycles):
                    yv, lv = ys[key][t], ln[key][t]
                    if yv is None and key.startswith("out:"):
                        res.unknown_outputs += 1     # x in Yosys (e.g. undriven bits): not comparable
                        continue
                    if yv != lv:
                        res.mismatches.append(f"seed {seed} cycle {t}: {key} yosys={yv} lean={lv}")
                        break
    return res
