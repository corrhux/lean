"""Web app API tests (FastAPI TestClient; no browser)."""

import os
import shutil
import sys
from pathlib import Path

import pytest

fastapi = pytest.importorskip("fastapi")
from fastapi.testclient import TestClient  # noqa: E402

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO))
from app.backend.main import app  # noqa: E402

client = TestClient(app)
HAVE_LEAN = bool(os.environ.get("LAKE") or shutil.which("lake") or (Path.home() / ".elan/bin/lake").exists())


def test_index_and_static():
    r = client.get("/")
    assert r.status_code == 200 and "Proof" in r.text
    assert client.get("/static/app.js").status_code == 200


def test_designs_listed_with_files():
    names = {d["name"]: d for d in client.get("/api/designs").json()}
    assert {"counter", "fifo", "mul", "arbiter"} <= set(names)
    c = names["counter"]
    assert c["solution"] == "RtlProof/Examples/Counter/Solution.lean"
    assert c["exercise"].endswith("Exercise.lean") and "p_le_9" in c["theorems"]


def test_file_reads_are_sandboxed():
    assert client.get("/api/file", params={"path": "rtl/counter/counter.sv"}).status_code == 200
    assert client.get("/api/file", params={"path": "../etc/passwd"}).status_code == 404
    assert client.get("/api/file", params={"path": ".git/config"}).status_code == 404


def test_docs_list_has_course():
    paths = [d["path"] for d in client.get("/api/docs-list").json()]
    assert paths[0] == "course/README.md" and "docs/LEAN_FLUENCY.md" in paths


def test_satlab_zoo_small():
    r = client.post("/api/satlab/zoo", json={"kind": "mul-miter", "width": 4, "timeout": 30,
                                            "solvers": ["minisat22", "teach-cdcl", "not-a-solver"]})
    body = r.json()
    assert r.status_code == 200 and body["clauses"] > 0
    assert [row["solver"] for row in body["rows"]] == ["minisat22", "teach-cdcl"]
    assert {row["result"] for row in body["rows"]} == {"UNSAT"}


def test_satlab_rejects_bad_kind():
    assert client.post("/api/satlab/zoo", json={"kind": "rm -rf"}).status_code == 422


def test_tutor_reports_missing_key(monkeypatch):
    monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)
    monkeypatch.delenv("ANTHROPIC_AUTH_TOKEN", raising=False)
    r = client.post("/api/tutor", json={"question": "hi"})
    assert r.status_code == 503 and "ANTHROPIC_API_KEY" in r.json()["detail"]


@pytest.mark.skipif(not HAVE_LEAN, reason="needs Lean")
def test_lean_check():
    ok = client.post("/api/lean/check", json={"code": "example : 1 + 1 = 2 := rfl"}).json()
    assert ok["ok"]
    bad = client.post("/api/lean/check", json={"code": "example : 1 + 1 = 3 := rfl"}).json()
    assert not bad["ok"]


def test_every_listed_doc_is_readable():
    for d in client.get("/api/docs-list").json():
        assert client.get("/api/file", params={"path": d["path"]}).status_code == 200, d["path"]
