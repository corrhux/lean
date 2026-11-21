"""Solver event traces: recording, saving as JSON Lines, and pretty-printing.

Event kinds (all literals in DIMACS form):

    decide     {"lit", "level"}                  branch on a literal
    propagate  {"lit", "level", "reason"}        unit propagation; reason = clause
    conflict   {"clause", "level"}               all literals of a clause are false
    learn      {"clause", "uip", "lbd", "backjump"}   CDCL: learned clause (1UIP)
    backtrack  {"to"}                            DPLL: chronological backtrack
    backjump   {"to"}                            CDCL: non-chronological backjump
    flip       {"lit", "level"}                  DPLL: try the other branch
    restart    {"conflicts"}
    reduce     {"removed", "kept"}               learned-clause database reduction
    result     {"sat"}                           true / false / null (limit hit)
"""

from __future__ import annotations

import json
from typing import Any, Dict, Iterable, List, Optional, TextIO

Event = Dict[str, Any]


class Trace:
    """Collects events. Disabled traces cost one attribute check per event."""

    def __init__(self, enabled: bool = True, limit: Optional[int] = None):
        self.enabled = enabled
        self.limit = limit
        self.events: List[Event] = []
        self.truncated = False

    def emit(self, ev: str, **data: Any) -> None:
        if not self.enabled:
            return
        if self.limit is not None and len(self.events) >= self.limit:
            self.truncated = True
            return
        data["ev"] = ev
        self.events.append(data)

    def dump(self, fp: TextIO) -> None:
        for e in self.events:
            fp.write(json.dumps(e) + "\n")


def load(fp: TextIO) -> List[Event]:
    return [json.loads(line) for line in fp if line.strip()]


def _clause(c: Iterable[int], names: Optional[Dict[int, str]] = None) -> str:
    def lit(l: int) -> str:
        if names and abs(l) in names:
            return ("¬" if l < 0 else "") + names[abs(l)]
        return str(l)

    return "(" + " ∨ ".join(lit(l) for l in c) + ")"


def format_event(e: Event, names: Optional[Dict[int, str]] = None) -> str:
    def lit(l: int) -> str:
        if names and abs(l) in names:
            return ("¬" if l < 0 else "") + names[abs(l)]
        return str(l)

    k = e["ev"]
    indent = "  " * min(int(e.get("level", 0)), 30)
    if k == "decide":
        return f"{indent}DECIDE    {lit(e['lit'])}   @ level {e['level']}"
    if k == "propagate":
        return f"{indent}  imply   {lit(e['lit'])}   because {_clause(e['reason'], names)}"
    if k == "conflict":
        return f"{indent}CONFLICT  {_clause(e['clause'], names)} is all-false"
    if k == "learn":
        return (f"LEARN     {_clause(e['clause'], names)}  (1UIP {lit(e['uip'])}, "
                f"LBD {e['lbd']}, backjump to level {e['backjump']})")
    if k == "backjump":
        return f"BACKJUMP  to level {e['to']}"
    if k == "backtrack":
        return f"BACKTRACK to level {e['to']}"
    if k == "flip":
        return f"{indent}FLIP      try {lit(e['lit'])}   @ level {e['level']}"
    if k == "restart":
        return f"RESTART   after {e['conflicts']} conflicts"
    if k == "reduce":
        return f"REDUCE    removed {e['removed']} learned clauses, kept {e['kept']}"
    if k == "result":
        verdict = {True: "SAT", False: "UNSAT", None: "UNKNOWN (limit)"}[e["sat"]]
        return f"RESULT    {verdict}"
    return json.dumps(e)


def render(events: Iterable[Event], names: Optional[Dict[int, str]] = None) -> str:
    return "\n".join(format_event(e, names) for e in events)
