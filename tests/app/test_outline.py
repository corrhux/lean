"""The course path (course/outline.json): every chapter's reading and actions must resolve."""

import json
import sys
from pathlib import Path

import pytest

pytest.importorskip("fastapi")
REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO))
from fastapi.testclient import TestClient  # noqa: E402
from app.backend.main import app, doc_section  # noqa: E402

client = TestClient(app)
OUTLINE = json.loads((REPO / "course" / "outline.json").read_text())
CHAPTERS = [ch for p in OUTLINE["parts"] for ch in p["chapters"]]


def test_chapter_ids_unique_and_in_parts_order():
    ids = [c["id"] for c in CHAPTERS]
    assert len(ids) == len(set(ids))
    assert [p["id"] for p in OUTLINE["parts"]] == ["A", "B", "C", "D", "E"]


@pytest.mark.parametrize("ch", CHAPTERS, ids=[c["id"] for c in CHAPTERS])
def test_chapter_resolves(ch):
    r = client.get(f"/api/course/{ch['id']}")
    assert r.status_code == 200, r.text
    body = r.json()
    assert len(body["sections"]) == len(ch["read"]) and all(s["text"].strip() for s in body["sections"])
    designs = {d["name"] for d in client.get("/api/designs").json()}
    files = {w["path"] for w in client.get("/api/workbook").json()} | {""}
    for a in ch["do"]:
        assert a["view"] in {"twins", "lean", "sat", "exam", "docs"}
        if a["view"] == "twins":
            assert a["design"] in designs and a.get("tab", "verdicts") in {"verdicts", "rtl", "lean", "bench"}
        if a["view"] == "lean":
            assert a["file"] in files
        if a["view"] == "sat":
            assert a.get("lab") in {1, 2, 3, 4, 5} or a.get("zoo")
        if a["view"] == "docs":
            assert (REPO / a["doc"]).is_file()


def test_section_extraction_ignores_code_fences():
    text = "# T\n\n## A1 one\nx\n```sh\n# not a heading\n```\ny\n## A2 two\nz\n"
    assert doc_section(text, "A1") == "## A1 one\nx\n```sh\n# not a heading\n```\ny\n"
    assert doc_section(text, "A3") is None
