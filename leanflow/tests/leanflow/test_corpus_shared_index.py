"""Cover the cross-batch shared-declaration index."""

from __future__ import annotations

import json

from leanflow_cli.formalization import corpus_shared_index

_BATCH_TEMPLATE = """import Mathlib

namespace Demo

{body}

end Demo
"""


def _write_batch(root, batch_id: str, body: str) -> None:
    directory = root / "FateXWork" / "Environments" / batch_id
    directory.mkdir(parents=True, exist_ok=True)
    (directory / "Main.lean").write_text(_BATCH_TEMPLATE.format(body=body), encoding="utf-8")


def _project(tmp_path):
    root = tmp_path / "project"
    root.mkdir()
    return root


def test_index_collects_sorry_free_declarations(tmp_path):
    root = _project(tmp_path)
    _write_batch(root, "items-a", "def sharedNorm (x : ℝ) : ℝ := |x|")
    _write_batch(root, "items-b", "theorem helper (x : ℝ) : x = x := rfl")

    entries = corpus_shared_index.scan_project_declarations(root)
    names = {entry.name for entry in entries}

    assert "sharedNorm" in names
    assert "helper" not in names  # theorems are not indexed as reusable vocabulary


def test_index_excludes_declarations_that_still_carry_sorry(tmp_path):
    """An unfinished scaffold must never be offered as a reusable asset."""
    root = _project(tmp_path)
    _write_batch(root, "items-a", "def partialNorm (x : ℝ) : ℝ := by\n  sorry")
    _write_batch(root, "items-b", "def finishedNorm (x : ℝ) : ℝ := |x|")

    names = {entry.name for entry in corpus_shared_index.scan_project_declarations(root)}

    assert "finishedNorm" in names
    assert "partialNorm" not in names


def test_duplicate_groups_require_the_same_signature_across_batches(tmp_path):
    """Batches that define the same signature are grouped; different ones are not."""
    root = _project(tmp_path)
    _write_batch(root, "items-a", "def norm (x : ℝ) : ℝ := |x|")
    _write_batch(root, "items-b", "def norm (x : ℝ) : ℝ := Real.sqrt (x ^ 2)")
    _write_batch(root, "items-c", "def norm (x : ℤ) : ℤ := x")

    payload = corpus_shared_index.refresh_index(root)
    groups = corpus_shared_index.duplicate_groups(payload["entries"])

    grouped_batches = sorted(
        batch for group in groups.values() for batch in {entry["batch_id"] for entry in group}
    )
    assert grouped_batches == ["items-a", "items-b"]
    assert "items-c" not in grouped_batches


def test_same_name_with_different_signature_is_not_merged(tmp_path):
    """A shared name is not identity: the corpus proved this 160 times over."""
    root = _project(tmp_path)
    _write_batch(root, "items-a", "def margin (x : ℝ) : ℝ := |x|")
    _write_batch(root, "items-b", "def margin (x : ℤ) : ℤ := x")

    payload = corpus_shared_index.refresh_index(root)

    assert corpus_shared_index.duplicate_groups(payload["entries"]) == {}


def test_refresh_is_incremental_and_reports_no_change(tmp_path):
    """An unchanged project must not rewrite the index."""
    root = _project(tmp_path)
    _write_batch(root, "items-a", "def norm (x : ℝ) : ℝ := |x|")

    first = corpus_shared_index.refresh_index(root)
    second = corpus_shared_index.refresh_index(root)

    assert first["changed"] is True
    assert second["changed"] is False
    assert second["entries"] == first["entries"]


def test_refresh_rescans_only_when_a_source_changes(tmp_path):
    root = _project(tmp_path)
    _write_batch(root, "items-a", "def norm (x : ℝ) : ℝ := |x|")
    corpus_shared_index.refresh_index(root)

    _write_batch(root, "items-b", "def other (x : ℝ) : ℝ := x")
    third = corpus_shared_index.refresh_index(root)

    assert third["changed"] is True
    assert {entry["name"] for entry in third["entries"]} == {"norm", "other"}


def test_index_lives_outside_every_batch_plan_state(tmp_path):
    """The index must not inherit the per-batch isolation it exists to bridge."""
    root = _project(tmp_path)

    assert "campaign-plan-state" not in str(corpus_shared_index.index_path(root))


def test_corrupt_index_is_rebuilt_rather_than_trusted(tmp_path):
    root = _project(tmp_path)
    _write_batch(root, "items-a", "def norm (x : ℝ) : ℝ := |x|")
    corpus_shared_index.refresh_index(root)

    corpus_shared_index.index_path(root).write_text("{ not json", encoding="utf-8")
    assert corpus_shared_index.load_index(root)["entries"] == []

    rebuilt = corpus_shared_index.refresh_index(root)
    assert {entry["name"] for entry in rebuilt["entries"]} == {"norm"}


def test_index_never_stores_declaration_bodies(tmp_path):
    """The index is a cache of identities, not a copy of the corpus."""
    root = _project(tmp_path)
    _write_batch(root, "items-a", "def norm (x : ℝ) : ℝ := |x|")
    corpus_shared_index.refresh_index(root)

    stored = json.loads(corpus_shared_index.index_path(root).read_text(encoding="utf-8"))

    serialized = json.dumps(stored)
    assert "|x|" not in serialized
    assert stored["entries"][0]["signature_sha256"]


def test_summary_reports_duplicate_occurrences(tmp_path):
    root = _project(tmp_path)
    _write_batch(root, "items-a", "def norm (x : ℝ) : ℝ := |x|")
    _write_batch(root, "items-b", "def norm (x : ℝ) : ℝ := Real.sqrt (x ^ 2)")
    corpus_shared_index.refresh_index(root)

    summary = corpus_shared_index.index_summary(root)

    assert summary["duplicate_groups"] == 1
    assert summary["duplicate_occurrences"] == 2
