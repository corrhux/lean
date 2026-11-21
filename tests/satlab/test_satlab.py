import itertools
import os

import pytest

from satlab import cdcl, certs, dpll, gen, trace, zoo
from satlab.cli import main
from satlab.cnf import CNF, bv_value

OPTION_SETS = [
    cdcl.Options(),
    cdcl.Options(branching="ordered", restarts="none", phase_saving=False),
    cdcl.Options(branching="random", restarts="glucose", minimize=False, seed=3),
    cdcl.Options(reduce=False, luby_unit=4),
]


def reference(cnf: CNF) -> bool:
    from pysat.solvers import Solver

    with Solver(name="minisat22", bootstrap_with=cnf.clauses) as s:
        return s.solve()


# ------------------------------------------------------------------ CNF / I/O
def test_dimacs_roundtrip():
    cnf = gen.add_comm_miter(3)
    back = CNF.from_dimacs(cnf.to_dimacs(["hello"]))
    assert back.num_vars == cnf.num_vars
    assert back.clauses == cnf.clauses
    assert back.names == cnf.names


def test_luby_prefix():
    assert [cdcl.luby(i) for i in range(15)] == [1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8]


# ----------------------------------------------------- encoders (exhaustive)
@pytest.mark.parametrize("op", ["add", "mul", "ult", "eq"])
def test_bitvector_encoders_exhaustive(op):
    w = 3
    cnf = CNF()
    x, y = cnf.new_bv(w, "x"), cnf.new_bv(w, "y")
    if op == "add":
        out = cnf.bv_add(x, y)
    elif op == "mul":
        out = cnf.bv_mul(x, y)
    elif op == "ult":
        out = [cnf.bv_ult(x, y)]
    else:
        out = [cnf.bv_eq(x, y)]
    s = cdcl.Solver(cnf)
    for a, b in itertools.product(range(2 ** w), repeat=2):
        assume = [l if (a >> i) & 1 else -l for i, l in enumerate(x)]
        assume += [l if (b >> i) & 1 else -l for i, l in enumerate(y)]
        r = s.solve(assumptions=assume)
        assert r.sat
        got = bv_value(r.model, out)
        want = {"add": (a + b) % 2 ** w, "mul": (a * b) % 2 ** w,
                "ult": int(a < b), "eq": int(a == b)}[op]
        assert got == want, (op, a, b)


# ------------------------------------------- solvers agree with a reference
@pytest.mark.parametrize("seed", range(60))
def test_random_3sat_agrees_with_minisat(seed):
    n = 12 + seed % 15
    m = int(n * (3.6 + (seed % 7) * 0.2))
    cnf = gen.random_ksat(n, m, 3, seed)
    expected = reference(cnf)
    r = dpll.solve(cnf)
    assert r.sat == expected
    if r.sat:
        assert cnf.satisfied_by(r.model)
    for opts in OPTION_SETS:
        r = cdcl.solve(cnf, opts)
        assert r.sat == expected
        if r.sat:
            assert cnf.satisfied_by(r.model)


@pytest.mark.parametrize("seed", range(25))
def test_unsat_proofs_check(seed):
    cnf = gen.random_ksat(20, 110, 3, 1000 + seed)       # ratio 5.5: mostly UNSAT
    s = cdcl.Solver(cnf, cdcl.Options(proof=True, luby_unit=8))
    r = s.solve()
    assert r.sat == reference(cnf)
    if r.sat is False:
        res = certs.check_drup(cnf, certs.parse_drup(s.drup()))
        assert res.ok, res.message


def test_corrupted_proof_is_rejected():
    cnf = gen.pigeonhole(3)
    s = cdcl.Solver(cnf, cdcl.Options(proof=True))
    assert s.solve().sat is False
    good = certs.parse_drup(s.drup())
    assert certs.check_drup(cnf, good).ok
    assert not certs.check_drup(cnf, [("a", [1])]).ok      # not implied
    assert not certs.check_drup(cnf, []).ok or len(cnf.clauses) == 0


def test_pigeonhole_unsat_both_solvers():
    for n in range(1, 5):
        cnf = gen.pigeonhole(n)
        assert dpll.solve(cnf).sat is False
        assert cdcl.solve(cnf).sat is False


def test_empty_and_trivial_formulas():
    assert cdcl.solve(CNF(0, [])).sat is True
    assert cdcl.solve(CNF(1, [[]])).sat is False
    assert dpll.solve(CNF(1, [[]])).sat is False
    assert cdcl.solve(CNF(1, [[1], [-1]])).sat is False


# ------------------------------------------------------------ hardware flavour
def test_counter_bmc_correct_design_holds():
    assert cdcl.solve(gen.counter_bmc(14, wrap=9).cnf).sat is False


def test_counter_bmc_bug_gives_counterexample():
    inst = gen.counter_bmc(12, wrap=10)
    r = cdcl.solve(inst.cnf)
    assert r.sat
    rows = inst.decode(r.model)
    assert rows[0]["cnt"] == 0
    assert max(row["cnt"] for row in rows) > 9
    for prev, cur in zip(rows, rows[1:]):                     # replay the RTL
        nxt = prev["cnt"] if not prev["en"] else (0 if prev["cnt"] == 10 else (prev["cnt"] + 1) % 16)
        assert cur["cnt"] == nxt


def test_counter_bug_needs_depth_10():
    assert cdcl.solve(gen.counter_bmc(9, wrap=10).cnf).sat is False
    assert cdcl.solve(gen.counter_bmc(10, wrap=10).cnf).sat is True


def test_commutativity_miters_unsat():
    for w in range(1, 5):
        assert cdcl.solve(gen.add_comm_miter(w)).sat is False
        assert cdcl.solve(gen.mul_comm_miter(w)).sat is False


# ------------------------------------------------------------- incremental
def test_incremental_assumptions_and_failed_core():
    cnf = CNF(3, [[-1, 2], [-2, 3]])                 # 1 → 2 → 3
    s = cdcl.Solver(cnf)
    assert s.solve(assumptions=[1]).sat
    r = s.solve(assumptions=[1, -3])
    assert r.sat is False
    assert set(r.failed_assumptions) <= {1, -3} and r.failed_assumptions
    assert s.solve(assumptions=[-3]).sat              # still SAT without 1
    s.add_clause([1])
    assert s.solve(assumptions=[-3]).sat is False
    assert s.solve().sat


# ---------------------------------------------------------------- tracing
def test_trace_events_are_well_formed():
    tr = trace.Trace()
    cdcl.solve(gen.pigeonhole(3), trace=tr)
    kinds = {e["ev"] for e in tr.events}
    assert {"decide", "propagate", "conflict", "learn", "result"} <= kinds
    assert tr.events[-1] == {"ev": "result", "sat": False}
    text = trace.render(tr.events, gen.pigeonhole(3).names)
    assert "LEARN" in text and "p0h0" in text


# ------------------------------------------------------------------- zoo
def test_zoo_solvers_agree():
    rows = zoo.run(gen.mul_comm_miter(4), ["minisat22", "cadical195", "kissat404", "z3", "teach-cdcl"],
                   timeout=60)
    assert zoo.consistent(rows) == "UNSAT", rows
    assert "solver" in zoo.table(rows)


# ------------------------------------------------------------------- CLI
def test_cli_end_to_end(tmp_path, capsys):
    cnf_path, proof, tr = (os.fspath(tmp_path / n) for n in ("m.cnf", "m.drup", "m.jsonl"))
    assert main(["gen", "mul-miter", "--width", "3", "-o", cnf_path]) == 0
    assert main(["solve", cnf_path, "--proof", proof, "--trace", tr]) == 20
    assert main(["check", cnf_path, proof]) == 0
    assert main(["trace", tr, "--names", cnf_path]) == 0
    assert main(["ablate", cnf_path]) == 0
    out = capsys.readouterr().out
    assert "UNSATISFIABLE" in out and "OK:" in out and "no restarts" in out
