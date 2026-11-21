"""`satlab` command-line interface.

Examples:
    satlab gen mul-miter --width 8 -o mul8.cnf
    satlab gen counter-bmc --depth 12 --wrap 10 -o bug.cnf
    satlab solve bug.cnf --solver cdcl --trace bug.jsonl --proof bug.drup
    satlab trace bug.jsonl --names bug.cnf | less
    satlab check mul8.cnf mul8.drup
    satlab zoo mul8.cnf --timeout 20
    satlab ablate mul8.cnf          # CDCL with each technique switched off
"""

from __future__ import annotations

import argparse
import json
import sys
from typing import List, Optional

from . import cdcl, certs, dpll, gen, trace, zoo
from .cnf import CNF


def _read(path: str) -> CNF:
    with open(path) as f:
        return CNF.from_dimacs(f.read())


def cmd_gen(a: argparse.Namespace) -> int:
    comments: List[str] = [f"satlab gen {a.kind}"]
    if a.kind == "pigeonhole":
        cnf = gen.pigeonhole(a.n)
    elif a.kind == "random":
        cnf = gen.random_ksat(a.n, a.m, a.k, a.seed)
    elif a.kind == "add-miter":
        cnf = gen.add_comm_miter(a.width)
    elif a.kind == "mul-miter":
        cnf = gen.mul_comm_miter(a.width)
    else:
        cnf = gen.counter_bmc(a.depth, a.wrap).cnf
    text = cnf.to_dimacs(comments)
    if a.output:
        with open(a.output, "w") as f:
            f.write(text)
        print(f"wrote {a.output}: {cnf.num_vars} vars, {len(cnf.clauses)} clauses")
    else:
        sys.stdout.write(text)
    return 0


def cmd_solve(a: argparse.Namespace) -> int:
    cnf = _read(a.file)
    tr = trace.Trace(enabled=bool(a.trace), limit=a.trace_limit)
    if a.solver == "dpll":
        r = dpll.solve(cnf, tr, a.max_conflicts)
        stats = vars(r.stats)
        sat, model = r.sat, r.model
    else:
        opts = cdcl.Options(branching=a.branching, restarts=a.restarts,
                            phase_saving=not a.no_phase_saving, minimize=not a.no_minimize,
                            reduce=not a.no_reduce, proof=bool(a.proof), seed=a.seed)
        s = cdcl.Solver(cnf, opts, tr)
        r = s.solve(max_conflicts=a.max_conflicts)
        stats = vars(r.stats)
        sat, model = r.sat, r.model
        if a.proof and sat is False:
            with open(a.proof, "w") as f:
                f.write(s.drup())
    print({True: "s SATISFIABLE", False: "s UNSATISFIABLE", None: "s UNKNOWN"}[sat])
    if sat and a.model:
        print("v " + " ".join(str(v if model[v] else -v) for v in sorted(model)) + " 0")
    print("c " + json.dumps(stats))
    if a.trace:
        with open(a.trace, "w") as f:
            tr.dump(f)
        print(f"c trace: {len(tr.events)} events -> {a.trace}" + (" (truncated)" if tr.truncated else ""))
    return 10 if sat else 20 if sat is False else 0


def cmd_trace(a: argparse.Namespace) -> int:
    names = _read(a.names).names if a.names else None
    with open(a.file) as f:
        print(trace.render(trace.load(f), names))
    return 0


def cmd_check(a: argparse.Namespace) -> int:
    with open(a.proof) as f:
        res = certs.check_drup(_read(a.file), certs.parse_drup(f.read()))
    print(("OK: " if res.ok else "FAILED: ") + res.message)
    return 0 if res.ok else 1


def cmd_zoo(a: argparse.Namespace) -> int:
    rows = zoo.run(_read(a.file), a.solvers.split(",") if a.solvers else zoo.DEFAULT_SOLVERS, a.timeout)
    print(zoo.table(rows))
    if a.json:
        with open(a.json, "w") as f:
            json.dump(rows, f, indent=2)
    zoo.consistent(rows)
    return 0


def cmd_ablate(a: argparse.Namespace) -> int:
    cnf = _read(a.file)
    configs = {
        "full CDCL": cdcl.Options(),
        "no VSIDS (ordered)": cdcl.Options(branching="ordered"),
        "no restarts": cdcl.Options(restarts="none"),
        "glucose restarts": cdcl.Options(restarts="glucose"),
        "no phase saving": cdcl.Options(phase_saving=False),
        "no minimisation": cdcl.Options(minimize=False),
        "no DB reduction": cdcl.Options(reduce=False),
    }
    print(f"{'configuration':<22} {'result':<8} {'conflicts':>10} {'decisions':>10} {'learned lits':>13}")
    for label, opts in configs.items():
        r = cdcl.solve(cnf, opts, max_conflicts=a.max_conflicts)
        verdict = {True: "SAT", False: "UNSAT", None: "LIMIT"}[r.sat]
        print(f"{label:<22} {verdict:<8} {r.stats.conflicts:>10} {r.stats.decisions:>10} "
              f"{r.stats.learned_literals:>13}")
    return 0


def main(argv: Optional[List[str]] = None) -> int:
    p = argparse.ArgumentParser(prog="satlab", description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True)

    g = sub.add_parser("gen", help="generate an instance")
    g.add_argument("kind", choices=["pigeonhole", "random", "add-miter", "mul-miter", "counter-bmc"])
    g.add_argument("-n", type=int, default=5)
    g.add_argument("-m", type=int, default=21)
    g.add_argument("-k", type=int, default=3)
    g.add_argument("--seed", type=int, default=0)
    g.add_argument("--width", type=int, default=8)
    g.add_argument("--depth", type=int, default=12)
    g.add_argument("--wrap", type=int, default=9)
    g.add_argument("-o", "--output")
    g.set_defaults(fn=cmd_gen)

    s = sub.add_parser("solve", help="solve with the teaching DPLL or CDCL")
    s.add_argument("file")
    s.add_argument("--solver", choices=["cdcl", "dpll"], default="cdcl")
    s.add_argument("--branching", choices=["vsids", "ordered", "random"], default="vsids")
    s.add_argument("--restarts", choices=["none", "luby", "glucose"], default="luby")
    s.add_argument("--no-phase-saving", action="store_true")
    s.add_argument("--no-minimize", action="store_true")
    s.add_argument("--no-reduce", action="store_true")
    s.add_argument("--seed", type=int, default=0)
    s.add_argument("--max-conflicts", type=int)
    s.add_argument("--trace", help="write JSONL event trace")
    s.add_argument("--trace-limit", type=int, default=200000)
    s.add_argument("--proof", help="write DRUP proof (UNSAT only)")
    s.add_argument("--model", action="store_true", help="print the model")
    s.set_defaults(fn=cmd_solve)

    t = sub.add_parser("trace", help="pretty-print a trace")
    t.add_argument("file")
    t.add_argument("--names", help="CNF file whose 'c var' comments name variables")
    t.set_defaults(fn=cmd_trace)

    c = sub.add_parser("check", help="check a DRUP proof")
    c.add_argument("file")
    c.add_argument("proof")
    c.set_defaults(fn=cmd_check)

    z = sub.add_parser("zoo", help="compare real solvers")
    z.add_argument("file")
    z.add_argument("--solvers", help="comma-separated list")
    z.add_argument("--timeout", type=float, default=30.0)
    z.add_argument("--json")
    z.set_defaults(fn=cmd_zoo)

    ab = sub.add_parser("ablate", help="teaching CDCL with each technique disabled")
    ab.add_argument("file")
    ab.add_argument("--max-conflicts", type=int, default=200000)
    ab.set_defaults(fn=cmd_ablate)

    a = p.parse_args(argv)
    return a.fn(a)


if __name__ == "__main__":
    sys.exit(main())
