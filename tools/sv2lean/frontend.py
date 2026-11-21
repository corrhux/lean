"""Run Yosys to get a flat, single-clock, $dff-only JSON netlist."""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import Dict, Optional, Sequence

REPO = Path(__file__).resolve().parents[2]


def scratch_dir() -> str:
    """Temp dirs live under build/: the WebAssembly Yosys build cannot see /tmp."""
    d = REPO / "build" / "tmp"
    d.mkdir(parents=True, exist_ok=True)
    return str(d)


def yosys_binary() -> str:
    env = os.environ.get("YOSYS")
    if env:
        return env
    for name in ("yosys", "yowasp-yosys"):
        if shutil.which(name):
            return name
    raise RuntimeError("no Yosys found: install the OSS CAD Suite or `pip install yowasp-yosys`, "
                       "or set YOSYS=/path/to/yosys")


def run_yosys(script: str, cwd: Optional[Path] = None) -> str:
    p = subprocess.run([yosys_binary(), "-q", "-p", script], cwd=cwd,
                       capture_output=True, text=True)
    if p.returncode != 0:
        raise RuntimeError(f"yosys failed:\n{p.stdout}\n{p.stderr}")
    return p.stdout


def lower_script(files: Sequence[str], top: str, params: Dict[str, int], out_json: str,
                 frontend: str = "read -formal") -> str:
    steps = [f"{frontend} {f}" for f in files]
    steps += [f"chparam -set {k} {v} {top}" for k, v in params.items()]
    steps += [
        f"prep -top {top}",
        "flatten",
        "memory -nomap",
        "memory_map",          # memories → one register per word + read/write muxes
        "opt_clean",
        "async2sync",          # async resets → synchronous (single-clock semantics)
        "dffunmap",            # $sdff/$dffe/... → plain $dff + muxes
        "opt_clean -purge",
        f"write_json {out_json}",
    ]
    return "; ".join(steps)


def sv2v_binary() -> str:
    for cand in (os.environ.get("SV2V"), shutil.which("sv2v"), "/opt/sv2v/bin/sv2v"):
        if cand and (Path(cand).exists() or shutil.which(cand)):
            return cand
    raise RuntimeError("sv2v not found: install it from github.com/zachjs/sv2v/releases or set SV2V")


def sv2v(files: Sequence[str], out_path: str, includes: Sequence[str] = (),
         defines: Sequence[str] = ()) -> None:
    """Convert SystemVerilog that Yosys's own parser rejects (packages, assignment patterns,
    `unique case`, ...) to Verilog-2005, as Ibex's own synthesis and LEC flows do."""
    cmd = [sv2v_binary()] + [f"--define={d}" for d in defines] + [f"-I{i}" for i in includes] + list(files)
    p = subprocess.run(cmd, capture_output=True, text=True)
    if p.returncode != 0:
        raise RuntimeError(f"sv2v failed:\n{p.stderr}")
    Path(out_path).write_text(p.stdout)


def netlist_json(files: Sequence[str], top: str, params: Optional[Dict[str, int]] = None,
                 use_sv2v: bool = False, includes: Sequence[str] = (),
                 defines: Sequence[str] = ()) -> dict:
    """Lower the design and return the whole Yosys JSON document."""
    files = [str(Path(f).resolve()) for f in files]
    with tempfile.TemporaryDirectory(dir=scratch_dir()) as td:
        out = os.path.join(td, "netlist.json")
        if use_sv2v:
            conv = os.path.join(td, f"{top}.sv2v.v")
            sv2v(files, conv, [str(Path(i).resolve()) for i in includes], defines)
            files = [conv]
        run_yosys(lower_script(files, top, params or {}, out))
        with open(out) as f:
            data = json.load(f)
    if top not in data["modules"]:
        raise RuntimeError(f"top module {top!r} not in netlist: {list(data['modules'])}")
    return data
