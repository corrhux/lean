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


# ---------------------------------------------------------------- workspace, live Lean, waveform
HAVE_SBY = bool(shutil.which("sby") or shutil.which("yowasp-sby"))
COUNTER_SV = (REPO / "rtl/counter/counter.sv").read_text()
COUNTER_BUG = COUNTER_SV.replace("cnt == WRAP", "cnt == WRAP + 4'd1")    # counts to 10


def test_vcd_endpoint(tmp_path):
    d = REPO / "build" / "test_app"
    d.mkdir(parents=True, exist_ok=True)
    (d / "t.vcd").write_text("$scope module top $end\n$var wire 1 ! clk $end\n$var wire 4 \" cnt $end\n"
                             "$upscope $end\n$enddefinitions $end\n#0\n0!\nb0 \"\n#5\n1!\n#10\n0!\nb1 \"\n#15\n1!\n"
                             "#20\n0!\nb10 \"\n")
    w = client.get("/api/vcd", params={"path": "build/test_app/t.vcd"}).json()
    cnt = next(s for s in w["signals"] if s["short"] == "cnt")
    assert w["steps"] == 3 and cnt["width"] == 4 and cnt["values"] == ["0", "1", "10"]
    assert client.get("/api/vcd", params={"path": "../x.vcd"}).status_code == 404


def test_run_rejects_foreign_files():
    r = client.post("/api/designs/counter/run", json={"rtl": {"../../etc/passwd": "x"}})
    assert r.status_code == 400


@pytest.mark.skipif(not (HAVE_LEAN and HAVE_SBY), reason="needs Lean and SymbiYosys")
def test_edited_rtl_breaks_both_sides():
    rows = client.post("/api/designs/counter/run", json={"rtl": {"counter.sv": COUNTER_BUG}}).json()
    v = {(r["side"], r["task"], r["property"]): r for r in rows}
    assert v[("mc", "bmc", "p_le_9")]["status"] == "cex"
    # k = 4 induction cannot see a bug 10 cycles deep: Jasper's "undetermined", not a counterexample
    assert v[("mc", "prove", "p_le_9")]["status"] == "inconclusive"
    assert v[("lean", None, "p_le_9")]["status"] == "failed"
    assert "solution line" in v[("lean", None, "p_le_9")]["note"]
    assert v[("lean", None, "p_hold")]["status"] == "proved"


@pytest.mark.skipif(not HAVE_LEAN, reason="needs Lean")
def test_live_lean_sync_and_goal():
    code = "theorem t (x : Nat) (h : x = 1) : x + 0 = 1 := by\n  simp\n  exact h\nexample : 1 = 2 := rfl\n"
    r = client.post("/api/lean/sync", json={"key": "pytest", "code": code}).json()
    assert [d["line"] for d in r["diagnostics"] if d["severity"] == "error"] == [3]
    g = client.post("/api/lean/goal", json={"key": "pytest", "line": 1, "character": 2}).json()
    assert g["goals"] and "⊢ x + 0 = 1" in g["goals"][0]
    g = client.post("/api/lean/goal", json={"key": "pytest", "line": 2, "character": 2}).json()
    assert "⊢ x = 1" in g["goals"][0]
    assert client.post("/api/lean/sync", json={"key": "../x", "code": ""}).status_code == 422


@pytest.mark.skipif(not HAVE_LEAN, reason="needs Lean")
def test_live_twin_document_uses_regenerated_model():
    sol = (REPO / "RtlProof/Examples/Counter/Solution.lean").read_text()
    ok = client.post("/api/lean/sync", json={"key": "pytest-twin", "code": sol, "design": "counter"}).json()
    assert not ok["regenerated"] and not [d for d in ok["diagnostics"] if d["severity"] == "error"]
    bad = client.post("/api/lean/sync", json={"key": "pytest-twin", "code": sol, "design": "counter",
                                              "rtl": {"counter.sv": COUNTER_BUG}}).json()
    errs = [d for d in bad["diagnostics"] if d["severity"] == "error"]
    assert bad["regenerated"] and errs and not bad["model_diagnostics"]
    # positions are the solution's own lines: the failing step is a bv_decide in the solution
    assert all(sol.splitlines()[d["line"]].strip().startswith("bv_decide") for d in errs)


@pytest.mark.skipif(not (HAVE_LEAN and HAVE_SBY), reason="needs Lean and SymbiYosys")
def test_bench_one_value():
    r = client.post("/api/designs/mul/bench", json={"values": [4], "timeout": 120}).json()
    assert [row["value"] for row in r["rows"]] == ["4", "all"]
    assert r["rows"][0]["status"] == "PASS" and r["rows"][1]["status"] == "PROVED"
    assert client.get("/api/designs/mul/bench/last").json() == r


# ------------------------------------------------------------------ streamed tutor (fake SDK)
class _Stream:
    def __init__(self, texts, final):
        self.texts, self.final = texts, final

    def __iter__(self):
        from types import SimpleNamespace as NS
        return iter([NS(type="text", text=t) for t in self.texts])

    def get_final_message(self):
        return self.final


def _msg(content, stop):
    from types import SimpleNamespace as NS
    return NS(content=content, stop_reason=stop, model="claude-opus-5-5", stop_details=None,
              usage=NS(input_tokens=100, output_tokens=7, cache_read_input_tokens=90))


class _FakeClient:
    def __init__(self):
        from types import SimpleNamespace as NS
        self.kwargs = None
        self.beta = NS(messages=NS(tool_runner=self.tool_runner))

    def tool_runner(self, **kw):
        from types import SimpleNamespace as NS
        self.kwargs = kw
        assert kw["stream"] is True
        return [
            _Stream(["Let me ", "check."], _msg([NS(type="text", text="Let me check."),
                                                 NS(type="tool_use", name="check_lean", input={"code": "x"})],
                                                "tool_use")),
            _Stream(["It ", "compiles."], _msg([NS(type="text", text="It compiles.")], "end_turn")),
        ]


def test_tutor_stream_sse(monkeypatch):
    import json as _json
    import app.backend.main as m
    from tutor.client import Tutor
    monkeypatch.setenv("ANTHROPIC_API_KEY", "test-not-used")
    fake = _FakeClient()
    monkeypatch.setattr(m, "_TUTOR", Tutor(client=fake))
    r = client.post("/api/tutor/stream", json={"question": "why?", "level": 3, "context": "my scratchpad: X"})
    assert r.status_code == 200 and r.headers["content-type"].startswith("text/event-stream")
    events = [_json.loads(l[6:]) for l in r.text.split("\n") if l.startswith("data: ")]
    assert [e["type"] for e in events] == ["text", "text", "tool", "round", "text", "text", "done"]
    assert events[2]["label"] == "compiling Lean" and events[-1]["tools"] == ["check_lean"]
    sent = fake.kwargs["messages"][-1]["content"]
    assert "my scratchpad: X" in sent and "why?" in sent
    assert all(t.to_dict().get("eager_input_streaming") for t in fake.kwargs["tools"])
    assert m._TUTOR.history[-1] == {"role": "assistant", "content": "It compiles."}


# ----------------------------------------------------------------------- Ibex exam
def test_exam_files_listed():
    r = client.get("/api/exam").json()
    assert [p["name"] for p in r["parts"]] == ["MultDiv", "LoadStore"]
    assert sum(i["points"] for i in r["items"]) == 100


def test_exam_save_only_writes_exam_files():
    path = REPO / "RtlProof/Exam/Ibex/LoadStore.lean"
    original = path.read_text()
    try:
        assert client.post("/api/exam/save", json={"part": "LoadStore", "text": original + "-- x\n"}).status_code == 200
        assert path.read_text().endswith("-- x\n")
    finally:
        path.write_text(original)
    assert client.post("/api/exam/save", json={"part": "../../etc", "text": "x"}).status_code == 422


def test_app_does_not_serve_exam_solutions():
    assert client.get("/api/file", params={"path": "capstone/exam/solutions/MultDiv.lean"}).status_code == 404


@pytest.mark.skipif(not HAVE_LEAN, reason="needs Lean")
def test_exam_grade_blank():
    r = client.post("/api/exam/grade").json()
    assert r["total"] == 100 and r["score"] == 0 and not r["tampered"]
