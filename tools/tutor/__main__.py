"""tutor command line.

    tutor ask "Why does my induction step fail?" --file RtlProof/Examples/Counter/Exercise.lean --level 2
    tutor chat --design fifo --level 3
    ftwin tutor ...            (same thing)

Environment: ANTHROPIC_API_KEY (or an `ant auth login` profile); optional
TUTOR_MODEL (default claude-opus-5-5) and TUTOR_EFFORT (default medium).
"""

from __future__ import annotations

import argparse
import json
import sys

import anthropic

from .client import Tutor, eprint, explain_api_error
from .prompts import LADDER, user_message


def _show_tool(name: str, args: dict) -> None:
    detail = args.get("query") or args.get("path") or args.get("vcd_path") or args.get("design") or ""
    if name == "check_lean":
        detail = f"{len(args.get('code', '').splitlines())} lines"
    eprint(f"  · {name}({detail})")


def _report(turn, quiet: bool) -> None:
    print(turn.text)
    if not quiet:
        eprint(f"\n[{turn.served_by} · tools: {', '.join(turn.tool_calls) or 'none'} · "
               f"tokens in {turn.input_tokens} (cached {turn.cache_read_tokens}), out {turn.output_tokens}]")


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(prog="tutor", description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    for name in ("ask", "chat"):
        p = sub.add_parser(name)
        if name == "ask":
            p.add_argument("question")
        p.add_argument("--file", help="the file you are working on (repo-relative)")
        p.add_argument("--design", help="twin lab name, e.g. counter")
        p.add_argument("--level", type=int, choices=sorted(LADDER), default=2,
                       help="hint ladder: " + "; ".join(f"{k}={v.split(':')[0]}" for k, v in LADDER.items()))
        p.add_argument("--model")
        p.add_argument("--effort", choices=["low", "medium", "high", "xhigh", "max"])
        p.add_argument("--quiet", action="store_true")
        p.add_argument("--json", help="also write the answer and usage as JSON")
    a = ap.parse_args(argv)

    tutor = Tutor(model=a.model, effort=a.effort, on_tool=None if a.quiet else _show_tool)
    try:
        if a.cmd == "ask":
            turn = tutor.ask(user_message(a.question, a.level, a.file, a.design))
            _report(turn, a.quiet)
            if a.json:
                with open(a.json, "w") as f:
                    json.dump(turn.__dict__, f, indent=2)
            return 0 if turn.stop_reason != "refusal" else 2
        eprint("Tutor chat. Commands: /level N, /file PATH, /quit")
        level, file = a.level, a.file
        while True:
            try:
                q = input(f"\n[level {level}] you> ").strip()
            except EOFError:
                return 0
            if not q:
                continue
            if q in ("/quit", "/exit"):
                return 0
            if q.startswith("/level "):
                level = int(q.split()[1])
                continue
            if q.startswith("/file "):
                file = q.split(maxsplit=1)[1]
                continue
            _report(tutor.ask(user_message(q, level, file, a.design)), a.quiet)
            file = None            # attach the file once; later questions refer back to it
    except anthropic.APIError as e:
        eprint(explain_api_error(e))
        return 1


if __name__ == "__main__":
    sys.exit(main())
