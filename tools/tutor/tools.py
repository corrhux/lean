"""Local tools the tutor model can call. Plain functions, so they are testable
without the API; `client.py` wraps them for the SDK tool runner."""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import Dict, List, Optional, Tuple

REPO = Path(__file__).resolve().parents[2]
READABLE_DIRS = ("docs", "course", "capstone", "rtl", "RtlProof", "satlab", "tools", "tests")
READABLE_FILES = ("README.md",)
MAX_FILE_CHARS = 40_000
MAX_OUTPUT_CHARS = 12_000


def _lake() -> str:
    return os.environ.get("LAKE") or shutil.which("lake") or str(Path.home() / ".elan/bin/lake")


def _clip(text: str, limit: int = MAX_OUTPUT_CHARS) -> str:
    return text if len(text) <= limit else text[:limit] + f"\n… [{len(text) - limit} more characters]"


# ----------------------------------------------------------------- check_lean
def check_lean(code: str, timeout_s: int = 120) -> Dict[str, object]:
    """Compile a Lean snippet in the project environment.

    The snippet may import project modules (e.g. `import RtlProof`). If it has
    no imports, `import RtlProof` and `import Std.Tactic.BVDecide` are added.
    Returns {"ok", "errors", "warnings", "uses_sorry", "output"}.
    """
    src = code if re.search(r"^\s*import\s", code, re.M) else (
        "import RtlProof\nimport Std.Tactic.BVDecide\n\n" + code)
    work = REPO / "build" / "tutor"
    work.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=work, delete=False) as f:
        f.write(src)
        path = f.name
    try:
        p = subprocess.run([_lake(), "env", "lean", path], cwd=REPO, capture_output=True,
                           text=True, timeout=timeout_s)
        out = (p.stdout + p.stderr).replace(path, "<snippet>")
    except subprocess.TimeoutExpired:
        return {"ok": False, "errors": [f"timed out after {timeout_s}s"], "warnings": [],
                "uses_sorry": False, "output": ""}
    finally:
        os.unlink(path)
    errors = re.findall(r"<snippet>:\d+:\d+: error:.*?(?=\n<snippet>:\d+:\d+:|\Z)", out, re.S)
    warnings = re.findall(r"<snippet>:\d+:\d+: warning:.*?(?=\n<snippet>:\d+:\d+:|\Z)", out, re.S)
    return {
        "ok": p.returncode == 0 and not errors,
        "errors": [_clip(e.strip(), 3000) for e in errors],
        "warnings": [_clip(w.strip(), 1000) for w in warnings],
        "uses_sorry": "declaration uses 'sorry'" in out or "declaration uses `sorry`" in out,
        "output": _clip(out),
    }


# -------------------------------------------------------------- course_lookup
def _sections(md: str) -> List[Tuple[str, str]]:
    """Split Markdown into (heading, body) pairs at ## and ### headings."""
    parts: List[Tuple[str, str]] = []
    cur_head: Optional[str] = None
    cur: List[str] = []
    for line in md.splitlines():
        if re.match(r"^#{2,3} ", line):
            if cur_head is not None:
                parts.append((cur_head, "\n".join(cur)))
            cur_head, cur = line.lstrip("# ").strip(), []
        elif cur_head is not None:
            cur.append(line)
    if cur_head is not None:
        parts.append((cur_head, "\n".join(cur)))
    return parts


def course_lookup(query: str, max_sections: int = 3) -> str:
    """Return the course sections (docs/*.md) whose heading best matches `query`,
    e.g. "L12", "induction", "B5 certificates", "Sail", "SafePrefix"."""
    stop = {"the", "and", "for", "with", "what", "how", "why", "does", "is", "a", "an", "of", "to", "in"}
    words = [w.lower() for w in re.findall(r"[A-Za-z0-9_]+", query)
             if w.lower() not in stop and (len(w) > 2 or any(c.isdigit() for c in w))]
    if not words:
        return f"No course section matches {query!r}."
    scored = []
    for md in sorted((REPO / "docs").glob("*.md")):
        for head, body in _sections(md.read_text()):
            h, text = head.lower(), (head + "\n" + body).lower()
            if not all(w in text for w in words):       # every meaningful word must appear
                continue
            score = 10 * sum(w in h for w in words) + sum(text.count(w) for w in words)
            scored.append((score, md.name, head, body))
    scored.sort(key=lambda x: -x[0])
    if not scored:
        return f"No course section matches {query!r}."
    return "\n\n".join(f"[{name} § {head}]\n{_clip(body.strip(), 6000)}"
                       for _, name, head, body in scored[:max_sections])


# ------------------------------------------------------------------ read_file
def read_file(path: str) -> str:
    """Read a project file (docs, RTL, Lean, tools). Paths are repository-relative."""
    p = (REPO / path).resolve()
    rel = p.relative_to(REPO).parts if REPO in p.parents else ()
    if not rel or (rel[0] not in READABLE_DIRS and "/".join(rel) not in READABLE_FILES):
        return f"Refused: {path!r} is outside the readable project folders {READABLE_DIRS}."
    if not p.is_file():
        return f"No such file: {path}"
    return _clip(p.read_text(errors="replace"), MAX_FILE_CHARS)


# ---------------------------------------------------------------- cex_summary
def parse_vcd(text: str) -> Tuple[Dict[str, Tuple[str, int]], List[Tuple[int, Dict[str, str]]]]:
    """Minimal VCD reader: returns ({id: (name, width)}, [(time, {id: value})])."""
    sigs: Dict[str, Tuple[str, int]] = {}
    scope: List[str] = []
    changes: List[Tuple[int, Dict[str, str]]] = []
    cur: Dict[str, str] = {}
    t = None
    tokens = iter(text.split())
    for tok in tokens:
        if tok == "$scope":
            next(tokens)
            scope.append(next(tokens))
        elif tok == "$upscope":
            scope and scope.pop()
        elif tok == "$var":
            _kind, width, ident, name = next(tokens), int(next(tokens)), next(tokens), next(tokens)
            full = ".".join(scope[1:] + [name]) if len(scope) > 1 else name
            sigs.setdefault(ident, (full, width))
        elif tok.startswith("#"):
            if t is not None:
                changes.append((t, dict(cur)))
            t = int(tok[1:])
        elif tok[0] in "01xzXZ" and len(tok) > 1 and tok[1:] in sigs:
            cur[tok[1:]] = tok[0]
        elif tok[0] in "bB":
            ident = next(tokens)
            cur[ident] = tok[1:]
    if t is not None:
        changes.append((t, dict(cur)))
    return sigs, changes


def cex_summary(vcd_path: str, max_signals: int = 16) -> str:
    """Summarise a counterexample VCD as a per-step table of the design's signals."""
    p = (REPO / vcd_path).resolve()
    if REPO not in p.parents or not p.is_file():
        return f"No VCD at {vcd_path}"
    sigs, steps = parse_vcd(p.read_text())
    names = {}
    for ident, (name, width) in sigs.items():
        short = name.split(".")[-1]
        if short.startswith("$") or short.startswith("_"):
            continue
        names.setdefault(short, (ident, width))
    cols = sorted(names)[:max_signals]

    def val(v: Optional[str], width: int) -> str:
        if v is None:
            return "?"
        if set(v) <= {"0", "1"}:
            return str(int(v, 2)) if width > 1 else v
        return v

    clock_times = sorted({t for t, _ in steps})
    rows = ["step  " + "  ".join(f"{c:>8}" for c in cols)]
    for k, (t, vals) in enumerate(steps):
        if k % 2 == 1 and len(clock_times) > 2:   # one row per clock period
            continue
        rows.append(f"{k // 2:<5} " + "  ".join(f"{val(vals.get(names[c][0]), names[c][1]):>8}"
                                                for c in cols))
    return "\n".join(rows)


# ------------------------------------------------------------------ run_ftwin
def run_ftwin(design: str, timeout_s: int = 600) -> str:
    """Run `ftwin run <design>` (SymbiYosys tasks + Lean theorems) and return its table."""
    if not re.fullmatch(r"[a-z0-9_]+", design) or not (REPO / "rtl" / design / "twin.toml").is_file():
        return f"Unknown design {design!r}; available: " + ", ".join(
            sorted(p.parent.name for p in (REPO / "rtl").glob("*/twin.toml")))
    try:
        p = subprocess.run(["python3", "-m", "ftwin", "run", design], cwd=REPO,
                           capture_output=True, text=True, timeout=timeout_s,
                           env={**os.environ, "PYTHONPATH": str(REPO / "tools")})
    except subprocess.TimeoutExpired:
        return f"ftwin timed out after {timeout_s}s"
    return _clip(p.stdout + p.stderr)


def as_json(x: object) -> str:
    return x if isinstance(x, str) else json.dumps(x, indent=1)
