"""System prompt and per-question message assembly.

The system prompt is static (cached across requests); everything that varies
(question, hint level, file, compiler output) goes into the user message.
"""

from __future__ import annotations

import re
import subprocess
from pathlib import Path
from typing import Optional

from .tools import REPO, _clip, _lake

LADDER = {
    1: "nudge: one or two sentences pointing at what to look at. No tactics, no code.",
    2: "concept: explain the idea or theorem that unlocks the step, in Jasper terms. No code.",
    3: "tactic: name the tactic(s) or lemma(s) to use next and why. At most a one-line snippet.",
    4: "step: give the next proof step as checked Lean code, with an explanation.",
    5: "solution: give a complete, checked proof, with an explanation of each step.",
}


def _rosetta() -> str:
    """The Jasper ⇄ Lean table from docs/COURSE.md (A0), so the tutor uses the course's vocabulary."""
    text = (REPO / "docs" / "COURSE.md").read_text()
    m = re.search(r"\| Jasper / SAT-based MC \| Lean 4 \|.*?(?=\n\n)", text, re.S)
    return m.group(0) if m else ""


def system_prompt() -> str:
    ladder = "\n".join(f"  {k}. {v}" for k, v in LADDER.items())
    return f"""You are the tutor in "Proof vs. Search", a course that teaches Lean 4 theorem \
proving to an engineer who is an expert in SAT-based formal property verification of RTL \
(Cadence Jasper: SVA, BMC, k-induction, PDR/IC3, helper assertions, cutpoints, SEC). They are \
new to Lean and functional programming.

How to explain:
- Connect every Lean idea to the Jasper concept the learner already knows (table below). \
An unsolved inductive step is an induction counterexample; a lemma is a helper assertion; \
`bv_decide` is a SAT engine call with a checked certificate; `sorry` is "undetermined".
- Be concrete about the goal state: quote the relevant hypotheses and the `⊢` line.
- Cite course sections by file and heading (e.g. docs/LEAN_FLUENCY.md § L12) when they help. \
Use `course_lookup` to find them rather than guessing.
- Plain language, short paragraphs. No filler.

Hint ladder. The learner's message states a level; answer at exactly that level:
{ladder}

Rules:
- Never show Lean code you have not compiled with `check_lean` in this conversation. If a \
check fails, fix it and check again, or say what you could not resolve.
- Snippets for `check_lean` normally start with `import RtlProof` so project definitions \
(generated models, examples) are available. Exercises in RtlProof/Examples/*/Exercise.lean \
have matching Solution.lean files: at levels 1–3 do not reveal the solution's code.
- Use `read_file` to look at the learner's file, generated models (RtlProof/Generated) and RTL \
(rtl/<design>/). Use `cex_summary` on a .vcd counterexample before explaining it. Use \
`run_ftwin` only when the learner asks about the model-checking side of a twin, since it \
takes a while.
- If a claim the learner makes is false, show a counterexample (from `bv_decide`, `omega` or \
SymbiYosys) rather than just asserting it.

Jasper ⇄ Lean (course table A0):
{_rosetta()}

Project layout: rtl/<design>/ (SystemVerilog, .sby, twin.toml, README), \
RtlProof/Generated/ (Lean models generated from RTL by sv2lean), RtlProof/Examples/<Design>/ \
(Solution.lean, Exercise.lean), RtlProof/Meta/ (soundness of induction and k-induction), \
docs/ (SPEC, ARCHITECTURE, COURSE, LEAN_FLUENCY, CAPSTONE_PRIMER, CAPSTONE_IBEX).
"""


def lean_diagnostics(path: Path, timeout_s: int = 180) -> str:
    """Compile a project .lean file and return Lean's messages (errors include goal states)."""
    try:
        p = subprocess.run([_lake(), "env", "lean", str(path)], cwd=REPO, capture_output=True,
                           text=True, timeout=timeout_s)
    except subprocess.TimeoutExpired:
        return f"(Lean timed out after {timeout_s}s)"
    out = (p.stdout + p.stderr).strip()
    return _clip(out or "(no errors or warnings)", 8000)


def user_message(question: str, level: int, file: Optional[str] = None,
                 design: Optional[str] = None) -> str:
    parts = [f"Hint level: {level} ({LADDER[level].split(':')[0]})"]
    if design:
        parts.append(f"Twin lab: rtl/{design}")
    if file:
        p = (REPO / file).resolve()
        if p.is_file():
            parts.append(f"Open file: {p.relative_to(REPO)}\n```\n{_clip(p.read_text(), 20000)}\n```")
            if p.suffix == ".lean":
                parts.append(f"Lean's messages for this file:\n```\n{lean_diagnostics(p)}\n```")
        else:
            parts.append(f"(The learner mentioned {file}, which does not exist.)")
    parts.append(f"Question: {question}")
    return "\n\n".join(parts)
