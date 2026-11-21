"""satlab — teaching SAT solvers and experiments for course Part B.

Modules:
    cnf        CNF container, DIMACS I/O, Tseitin gate and bit-vector encoders
    dpll       textbook DPLL (chronological backtracking), with event trace
    cdcl       teaching CDCL: 2 watched literals, 1UIP learning, backjumping,
               VSIDS / restarts / phase saving / LBD reduction (each switchable),
               assumptions for incremental use, DRUP proof output
    certs      DRUP/DRAT proof writer and a forward RUP proof checker
    gen        instance generators (pigeonhole, random k-SAT, miters, counter BMC)
    zoo        run one CNF through several real solvers (PySAT, Z3) and the
               teaching solver; compare statistics
    trace      pretty-printer / stepper for solver event traces
    cli        `satlab` command-line entry point
"""

__all__ = ["cnf", "dpll", "cdcl", "certs", "gen", "zoo", "trace"]
