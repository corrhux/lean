#!/usr/bin/env python3
"""Compile the Lean code blocks in a Markdown document (SPEC FR-C2).

Rules for fenced blocks:
    ```lean          compiled, in document order, into one file
    ```lean fails    compiled on its own (after the blocks before it) and
                     must produce an error; used for teaching counter-examples
    ```lean skip     not compiled (pseudo-code or deliberately partial)

Usage:
    python tools/lean_blocks.py docs/LEAN_FLUENCY.md [--out build/lean_blocks]
Exit status is non-zero if a normal block fails or a `fails` block succeeds.
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import List, Tuple

FENCE = re.compile(r"^```lean(?:\s+(\w+))?\s*$")


def blocks(md: str) -> List[Tuple[int, str, str]]:
    out, cur, tag, start = [], None, "", 0
    for i, line in enumerate(md.splitlines(), 1):
        if cur is None:
            m = FENCE.match(line)
            if m:
                cur, tag, start = [], m.group(1) or "", i
        elif line.startswith("```"):
            out.append((start, tag, "\n".join(cur)))
            cur = None
        else:
            cur.append(line)
    return out


def _hoist_imports(src: str) -> str:
    """`import` must come first in a Lean file; move every import line to the top."""
    lines = src.splitlines()
    imports = sorted({l.strip() for l in lines if l.startswith("import ")})
    rest = [l for l in lines if not l.startswith("import ")]
    return "\n".join(imports + [""] + rest)


def lean(path: Path, root: Path) -> Tuple[bool, str]:
    lake = os.environ.get("LAKE", "lake")
    p = subprocess.run([lake, "env", "lean", str(path)], cwd=root, capture_output=True, text=True)
    text = p.stdout + p.stderr
    has_error = p.returncode != 0 or re.search(r":\d+:\d+: error", text) is not None
    return not has_error, text


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("markdown")
    ap.add_argument("--out", default="build/lean_blocks")
    a = ap.parse_args()
    root = Path(__file__).resolve().parent.parent
    md_path = Path(a.markdown)
    out = root / a.out / md_path.stem
    out.mkdir(parents=True, exist_ok=True)

    good: List[str] = []
    failures = 0
    for line, tag, code in blocks(md_path.read_text()):
        header = f"-- {md_path.name}:{line}\n"
        if tag == "skip":
            continue
        if tag == "fails":
            f = out / f"fails_{line}.lean"
            f.write_text(_hoist_imports("\n\n".join(good + [header + code])) + "\n")
            ok, text = lean(f, root)
            if ok:
                failures += 1
                print(f"UNEXPECTED SUCCESS: block at {md_path}:{line} is marked `fails` but compiled")
            else:
                print(f"ok (fails as intended): {md_path}:{line}")
            continue
        good.append(header + code)

    main_file = out / "All.lean"
    main_file.write_text(_hoist_imports("\n\n".join(good)) + "\n")
    ok, text = lean(main_file, root)
    # Map errors in All.lean back to the Markdown line of the enclosing block.
    if not ok:
        failures += 1
        src = main_file.read_text().splitlines()
        for m in re.finditer(r"All\.lean:(\d+):(\d+): error:?(.*)", text):
            ln = int(m.group(1))
            origin = next((s for s in reversed(src[:ln]) if s.startswith(f"-- {md_path.name}:")), "?")
            print(f"ERROR near {origin[3:]} (All.lean:{ln}):{m.group(3)}")
        print(text[-6000:])
    else:
        print(f"ok: {len(good)} blocks from {md_path} compile together")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
