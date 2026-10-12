"""Cover the per-module namespace that keeps generated statement files from colliding."""

from __future__ import annotations

from leanflow_cli.formalization.statement_module_namespace import (
    module_namespace,
    wrap_in_module_namespace,
)


def test_namespace_is_derived_from_the_item_directory():
    assert (
        module_namespace("FateXWork/Environments/Items730E8281E0/Main.lean")
        == "HDPItem.Items730E8281E0"
    )


def test_two_items_never_share_a_namespace():
    """The 2026-10-10 collision: two files both defined ``sourceEuclideanNorm``."""
    a = module_namespace("FateXWork/Environments/ItemsP17D1B04BA59F/Main.lean")
    b = module_namespace("FateXWork/Environments/Items00234CDA01A/Main.lean")
    assert a != b


def test_namespace_is_a_valid_lean_identifier_for_odd_directory_names():
    assert module_namespace("X/9-bad.name/Main.lean") == "HDPItem.M9_bad_name"


def test_header_stays_outside_and_declarations_move_inside():
    code = (
        "import Mathlib\n\n"
        "open scoped BigOperators\n"
        "set_option autoImplicit false\n\n"
        "noncomputable def euclideanNorm (x : Fin 2 → ℝ) : ℝ := 0\n\n"
        "theorem demo : True := by sorry\n"
    )
    wrapped = wrap_in_module_namespace(code, "HDPItem.Items1")
    head, _, rest = wrapped.partition("namespace HDPItem.Items1")
    assert "import Mathlib" in head
    assert "open scoped BigOperators" in head
    assert "set_option autoImplicit false" in head
    assert "def euclideanNorm" in rest and "theorem demo" in rest
    assert wrapped.rstrip().endswith("end HDPItem.Items1")


def test_a_model_chosen_namespace_is_nested_not_replaced():
    """``Source`` alone is reused by ten files, so it must not be the outermost scope."""
    code = "import Mathlib\n\nnamespace Source\n\ndef f : Nat := 1\n\nend Source\n"
    wrapped = wrap_in_module_namespace(code, "HDPItem.Items2")
    assert wrapped.index("namespace HDPItem.Items2") < wrapped.index("namespace Source")
    assert wrapped.rstrip().endswith("end HDPItem.Items2")


def test_wrapping_is_idempotent():
    code = "import Mathlib\n\ntheorem demo : True := by sorry\n"
    once = wrap_in_module_namespace(code, "HDPItem.Items3")
    assert wrap_in_module_namespace(once, "HDPItem.Items3") == once


def test_leading_block_comment_stays_in_the_header():
    code = "/- Book item 7.3\n  contraction -/\nimport Mathlib\n\ntheorem demo : True := by sorry\n"
    wrapped = wrap_in_module_namespace(code, "HDPItem.Items4")
    head = wrapped.split("namespace HDPItem.Items4")[0]
    assert "import Mathlib" in head and "contraction -/" in head


def test_header_only_file_is_left_alone():
    assert wrap_in_module_namespace("import Mathlib\n", "HDPItem.Items5") == "import Mathlib\n"
