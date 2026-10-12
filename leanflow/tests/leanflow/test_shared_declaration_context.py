"""Cover the shared-vocabulary prompt block."""

from __future__ import annotations

from leanflow_cli.formalization import corpus_shared_index
from leanflow_cli.workflows import shared_declaration_context

_BATCH_TEMPLATE = """import Mathlib

namespace Demo

{body}

end Demo
"""


def _write_shared(root, domain: str, body: str, *, namespace: str = "") -> None:
    directory = root / "FateXWork" / "Environments" / "Shared"
    directory.mkdir(parents=True, exist_ok=True)
    inner = f"namespace {namespace}\n\n{body}\n\nend {namespace}\n" if namespace else body
    (directory / f"{domain}.lean").write_text(f"import Mathlib\n\n{inner}\n", encoding="utf-8")


def _write_batch(root, batch_id: str, body: str) -> None:
    directory = root / "FateXWork" / "Environments" / batch_id
    directory.mkdir(parents=True, exist_ok=True)
    (directory / "Main.lean").write_text(_BATCH_TEMPLATE.format(body=body), encoding="utf-8")


def _project(tmp_path):
    root = tmp_path / "project"
    (root / "FateXWork" / "Environments").mkdir(parents=True)
    return root


def _refresh(root):
    return corpus_shared_index.refresh_index(root)


def test_empty_project_renders_nothing(tmp_path):
    """An unknown project must not inject a hollow header into every prompt."""
    root = _project(tmp_path)

    assert shared_declaration_context.prompt_block(root) == ""
    assert shared_declaration_context.prompt_block(None) == ""


def test_index_without_shared_declarations_renders_nothing(tmp_path):
    """Batches that never promoted anything have nothing to advertise."""
    root = _project(tmp_path)
    _write_batch(root, "items-a", "def localOnly (x : ℝ) : ℝ := |x|")
    corpus_shared_index.refresh_index(root)

    assert shared_declaration_context.prompt_block(root) == ""


def test_shared_declarations_are_listed_by_resolvable_namespace(tmp_path):
    """The block must name the namespace that actually reaches the symbol.

    Module name and namespace are independent in Lean: the file lives at
    ``FateXWork/Environments/Shared/Analysis.lean`` but its symbols sit in
    ``FateXWork.Shared.Analysis``. Naming the module would not resolve.
    """
    root = _project(tmp_path)
    _write_shared(
        root,
        "Analysis",
        "def euclideanNorm (x : ℝ) : ℝ := |x|",
        namespace="FateXWork.Shared.Analysis",
    )
    _write_shared(
        root,
        "Probability",
        "def gaussianWidth (x : ℝ) : ℝ := x",
        namespace="FateXWork.Shared.Probability",
    )
    corpus_shared_index.refresh_index(root)

    block = shared_declaration_context.prompt_block(root)

    assert block.startswith("[LEANFLOW SHARED VOCABULARY]")
    assert "`FateXWork.Shared.Analysis`" in block
    assert "`FateXWork.Shared.Probability`" in block
    assert "euclideanNorm" in block
    assert "gaussianWidth" in block
    # The path-derived module name is not what reaches these symbols.
    assert "FateXWork.Environments.Shared" not in block


def test_block_is_bounded_even_for_a_large_index(tmp_path):
    """A prompt must not grow with the corpus."""
    root = _project(tmp_path)
    body = "\n".join(f"def shared{i} (x : ℝ) : ℝ := x" for i in range(200))
    _write_shared(root, "Basic", body)
    corpus_shared_index.refresh_index(root)

    block = shared_declaration_context.prompt_block(root)

    assert len(block) < 4000
    assert "+" in block and "more" in block


def test_unbuilt_index_never_raises(tmp_path):
    """A missing or corrupt index degrades to no block, not to a crash."""
    root = _project(tmp_path)
    corpus_shared_index.index_path(root).parent.mkdir(parents=True, exist_ok=True)
    corpus_shared_index.index_path(root).write_text("{ not json", encoding="utf-8")

    assert shared_declaration_context.prompt_block(root) == ""


def test_prompt_block_reads_project_root_from_the_environment(tmp_path, monkeypatch):
    """Prompt assembly helpers in this package take no arguments.

    Callers concatenate the block unconditionally, so the root must come from
    ``LEANFLOW_PROJECT_ROOT`` when no argument is given.
    """
    root = _project(tmp_path)
    _write_shared(
        root,
        "Analysis",
        "def euclideanNorm (x : ℝ) : ℝ := |x|",
        namespace="FateXWork.Shared.Analysis",
    )
    corpus_shared_index.refresh_index(root)
    monkeypatch.setenv("LEANFLOW_PROJECT_ROOT", str(root))

    block = shared_declaration_context.prompt_block()

    assert "`FateXWork.Shared.Analysis`" in block
    assert "euclideanNorm" in block


def test_prompt_block_is_empty_without_a_resolvable_project(tmp_path, monkeypatch):
    monkeypatch.delenv("LEANFLOW_PROJECT_ROOT", raising=False)

    assert shared_declaration_context.prompt_block() == ""
    assert shared_declaration_context.summary() == {"entries": 0, "duplicate_groups": 0}
