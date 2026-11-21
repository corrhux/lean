"""Talk to Claude through the SDK's tool runner, with the local tools attached."""

from __future__ import annotations

import os
import sys
from dataclasses import dataclass, field
from typing import Callable, List, Optional

import anthropic
from anthropic import beta_tool

from . import tools
from .prompts import system_prompt

DEFAULT_MODEL = "claude-opus-5-5"
DEFAULT_EFFORT = "medium"          # Claude Opus 5.5's default; raise for hard proofs
FALLBACK_BETA = "server-side-fallback-2026-07-01"


@beta_tool
def check_lean(code: str) -> str:
    """Compile a Lean 4 snippet in the course project and report errors, warnings and
    whether it uses `sorry`. Start the snippet with `import RtlProof` to use project
    definitions; with no imports, `import RtlProof` and `import Std.Tactic.BVDecide`
    are added. Always check code before showing it to the learner.

    Args:
        code: Complete Lean source to compile.
    """
    return tools.as_json(tools.check_lean(code))


@beta_tool
def course_lookup(query: str) -> str:
    """Find course text (docs/*.md) by section heading or keyword, e.g. "L12 induction",
    "B5 certificates", "SafePrefix", "Sail".

    Args:
        query: Words to look for in section headings and text.
    """
    return tools.course_lookup(query)


@beta_tool
def read_file(path: str) -> str:
    """Read a project file: RTL (rtl/...), Lean (RtlProof/...), docs, or tools.

    Args:
        path: Repository-relative path, e.g. "RtlProof/Generated/Counter.lean".
    """
    return tools.read_file(path)


@beta_tool
def cex_summary(vcd_path: str) -> str:
    """Summarise a counterexample waveform (.vcd) as a table of signal values per step.

    Args:
        vcd_path: Repository-relative path to the .vcd file.
    """
    return tools.cex_summary(vcd_path)


@beta_tool
def run_ftwin(design: str) -> str:
    """Run both sides of a twin lab (SymbiYosys tasks and Lean theorems) and return the
    comparison table. Slow (tens of seconds); use only for model-checking questions.

    Args:
        design: Design name under rtl/, e.g. "counter", "fifo", "arbiter", "mul".
    """
    return tools.run_ftwin(design)


TOOLS = [check_lean, course_lookup, read_file, cex_summary, run_ftwin]


@dataclass
class Turn:
    text: str
    stop_reason: Optional[str]
    tool_calls: List[str] = field(default_factory=list)
    input_tokens: int = 0
    output_tokens: int = 0
    cache_read_tokens: int = 0
    served_by: Optional[str] = None


class Tutor:
    def __init__(self, model: Optional[str] = None, effort: Optional[str] = None,
                 client: Optional[anthropic.Anthropic] = None, max_iterations: int = 12,
                 on_tool: Optional[Callable[[str, dict], None]] = None):
        self.model = model or os.environ.get("TUTOR_MODEL", DEFAULT_MODEL)
        self.effort = effort or os.environ.get("TUTOR_EFFORT", DEFAULT_EFFORT)
        self.client = client or anthropic.Anthropic()
        self.max_iterations = max_iterations
        self.on_tool = on_tool
        self.system = [{"type": "text", "text": system_prompt(), "cache_control": {"type": "ephemeral"}}]
        self.history: List[dict] = []      # plain-text transcript of earlier questions/answers

    def ask(self, message: str) -> Turn:
        messages = self.history + [{"role": "user", "content": message}]
        kwargs = dict(
            model=self.model,
            max_tokens=16000,
            system=self.system,
            tools=TOOLS,
            messages=messages,
            output_config={"effort": self.effort},
            max_iterations=self.max_iterations,
        )
        if self.model.startswith(("claude-opus-5", "claude-fable-5", "claude-sonnet-5-5")):
            # Re-run on a fallback model if a safety classifier declines (beta).
            kwargs.update(betas=[FALLBACK_BETA], fallbacks="default")
        runner = self.client.beta.messages.tool_runner(**kwargs)

        turn = Turn(text="", stop_reason=None)
        last = None
        for msg in runner:
            last = msg
            u = msg.usage
            turn.input_tokens += u.input_tokens or 0
            turn.output_tokens += u.output_tokens or 0
            turn.cache_read_tokens += getattr(u, "cache_read_input_tokens", 0) or 0
            for block in msg.content:
                if block.type == "tool_use":
                    turn.tool_calls.append(block.name)
                    if self.on_tool:
                        self.on_tool(block.name, dict(block.input))
        if last is None:
            raise RuntimeError("no response from the model")
        turn.stop_reason = last.stop_reason
        turn.served_by = last.model
        if last.stop_reason == "refusal":
            cat = getattr(last.stop_details, "category", None) if last.stop_details else None
            turn.text = f"(The model declined to answer{f' — category {cat}' if cat else ''}.)"
        else:
            turn.text = "\n".join(b.text for b in last.content if b.type == "text").strip()
        if last.stop_reason == "tool_use":
            turn.text += f"\n\n(Stopped after {self.max_iterations} tool rounds; ask again to continue.)"
        self.history += [{"role": "user", "content": message},
                         {"role": "assistant", "content": turn.text or "(no answer)"}]
        return turn


def explain_api_error(e: Exception) -> str:
    if isinstance(e, anthropic.AuthenticationError):
        return "Authentication failed: set ANTHROPIC_API_KEY (or log in with `ant auth login`)."
    if isinstance(e, anthropic.PermissionDeniedError):
        return "This API key may not use that model."
    if isinstance(e, anthropic.NotFoundError):
        return "Model not found: check TUTOR_MODEL."
    if isinstance(e, anthropic.RateLimitError):
        return "Rate limited: wait a minute and ask again."
    if isinstance(e, anthropic.APIStatusError):
        return f"API error {e.status_code}: {e.message}"
    if isinstance(e, anthropic.APIConnectionError):
        return "Could not reach the API (network)."
    return f"{type(e).__name__}: {e}"


def eprint(*a: object) -> None:
    print(*a, file=sys.stderr, flush=True)
