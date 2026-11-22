"""A small Lean language-server client: one `lake env lean --server` per app.

The browser editor sends the whole document on every change; we forward it as
a full-text `didChange`, wait for Lean to finish elaborating (the
`$/lean/fileProgress` notification reports an empty `processing` list), and
return the diagnostics. Goals come from `$/lean/plainGoal` (tactic state) and
`$/lean/plainTermGoal` (expected type), the same requests the VS Code
infoview uses.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import threading
import time
from pathlib import Path
from typing import Any, Dict, List, Optional

REPO = Path(__file__).resolve().parents[2]
DOC_DIR = REPO / "build" / "app" / "lsp"


def _lake() -> str:
    return os.environ.get("LAKE") or shutil.which("lake") or str(Path.home() / ".elan/bin/lake")


class LeanServer:
    def __init__(self, timeout: float = 600):
        self.timeout = timeout
        self.proc: Optional[subprocess.Popen] = None
        self.lock = threading.Lock()            # one request/sync at a time from our side
        self.cv = threading.Condition()
        self.next_id = 0
        self.responses: Dict[int, Any] = {}
        self.diags: Dict[str, List[dict]] = {}
        self.versions: Dict[str, int] = {}
        self.progress_done: Dict[str, int] = {}  # uri -> version whose elaboration finished
        self.texts: Dict[str, str] = {}
        self.diag_version: Dict[str, int] = {}   # uri -> version of the last diagnostics message

    # ------------------------------------------------------------- transport
    def _start(self) -> None:
        if self.proc and self.proc.poll() is None:
            return
        self.proc = subprocess.Popen([_lake(), "env", "lean", "--server"], cwd=REPO,
                                     stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                     stderr=subprocess.DEVNULL)
        for d in (self.versions, self.progress_done, self.diags, self.texts, self.diag_version):
            d.clear()
        threading.Thread(target=self._reader, daemon=True).start()
        self._request("initialize", {"processId": os.getpid(), "rootUri": REPO.as_uri(),
                                     "capabilities": {}})
        self._notify("initialized", {})

    def _send(self, msg: dict) -> None:
        body = json.dumps(msg).encode()
        assert self.proc and self.proc.stdin
        self.proc.stdin.write(b"Content-Length: %d\r\n\r\n" % len(body) + body)
        self.proc.stdin.flush()

    def _reader(self) -> None:
        out = self.proc.stdout
        while True:
            length = None
            while True:
                line = out.readline()
                if not line:
                    with self.cv:
                        self.cv.notify_all()
                    return
                line = line.strip()
                if not line:
                    break
                if line.lower().startswith(b"content-length:"):
                    length = int(line.split(b":")[1])
            msg = json.loads(out.read(length))
            with self.cv:
                if "id" in msg and "method" not in msg:
                    self.responses[msg["id"]] = msg
                elif msg.get("method") == "textDocument/publishDiagnostics":
                    p = msg["params"]
                    if p.get("version") is None or p["version"] == self.versions.get(p["uri"]):
                        self.diags[p["uri"]] = p["diagnostics"]
                        self.diag_version[p["uri"]] = self.versions.get(p["uri"], -1)
                elif msg.get("method") == "$/lean/fileProgress":
                    p = msg["params"]
                    if not p["processing"]:
                        self.progress_done[p["textDocument"]["uri"]] = p["textDocument"].get("version", -1)
                elif "id" in msg and "method" in msg:        # server -> client request: acknowledge
                    self._send({"jsonrpc": "2.0", "id": msg["id"], "result": None})
                self.cv.notify_all()

    def _notify(self, method: str, params: dict) -> None:
        self._send({"jsonrpc": "2.0", "method": method, "params": params})

    def _request(self, method: str, params: dict, timeout: Optional[float] = None) -> Any:
        with self.cv:
            self.next_id += 1
            rid = self.next_id
        self._send({"jsonrpc": "2.0", "id": rid, "method": method, "params": params})
        deadline = time.monotonic() + (timeout or self.timeout)
        with self.cv:
            while rid not in self.responses:
                if self.proc.poll() is not None:
                    raise RuntimeError("the Lean server stopped")
                left = deadline - time.monotonic()
                if left <= 0:
                    raise TimeoutError(f"Lean did not answer {method} in time")
                self.cv.wait(left)
            msg = self.responses.pop(rid)
        if "error" in msg:
            raise RuntimeError(msg["error"].get("message", str(msg["error"])))
        return msg.get("result")

    # ------------------------------------------------------------------- API
    def uri(self, key: str) -> str:
        DOC_DIR.mkdir(parents=True, exist_ok=True)
        return (DOC_DIR / f"{key}.lean").as_uri()

    def sync(self, key: str, text: str) -> dict:
        """Send the document; wait until Lean has elaborated it; return diagnostics."""
        with self.lock:
            self._start()
            uri = self.uri(key)
            t0 = time.monotonic()
            if uri not in self.versions:
                self.versions[uri] = 1
                self.diags[uri] = []
                self._notify("textDocument/didOpen", {"textDocument": {
                    "uri": uri, "languageId": "lean4", "version": 1, "text": text}})
            elif self.texts.get(uri) != text:
                self.versions[uri] += 1
                self.diags[uri] = []
                self._notify("textDocument/didChange", {
                    "textDocument": {"uri": uri, "version": self.versions[uri]},
                    "contentChanges": [{"text": text}]})
            self.texts[uri] = text
            v = self.versions[uri]
            deadline = time.monotonic() + self.timeout
            with self.cv:
                while self.progress_done.get(uri) != v:
                    if self.proc.poll() is not None:
                        raise RuntimeError("the Lean server stopped")
                    left = deadline - time.monotonic()
                    if left <= 0:
                        raise TimeoutError("Lean is still elaborating; try again")
                    self.cv.wait(left)
                # the final diagnostics message can trail the progress notice
                settle = time.monotonic() + 3
                while self.diag_version.get(uri) != v and time.monotonic() < settle:
                    self.cv.wait(settle - time.monotonic())
                diags = list(self.diags.get(uri, []))
        return {"version": v, "seconds": round(time.monotonic() - t0, 2),
                "diagnostics": [_diag(d) for d in diags]}

    def goal(self, key: str, line: int, character: int) -> dict:
        """Tactic state and expected type at a position (0-based line and UTF-16 column)."""
        with self.lock:
            self._start()
            uri = self.uri(key)
            if uri not in self.versions:
                return {"goals": None, "term": None}
            pos = {"textDocument": {"uri": uri}, "position": {"line": line, "character": character}}
            g = self._request("$/lean/plainGoal", pos)
            t = self._request("$/lean/plainTermGoal", pos)
        return {"goals": g.get("goals") if g else None, "term": t.get("goal") if t else None}

    def close(self) -> None:
        if self.proc and self.proc.poll() is None:
            self.proc.kill()


def _diag(d: dict) -> dict:
    r = d["range"]
    sev = {1: "error", 2: "warning", 3: "information", 4: "hint"}.get(d.get("severity", 1), "error")
    return {"line": r["start"]["line"], "col": r["start"]["character"],
            "endLine": r["end"]["line"], "endCol": r["end"]["character"],
            "severity": sev, "message": d["message"]}
