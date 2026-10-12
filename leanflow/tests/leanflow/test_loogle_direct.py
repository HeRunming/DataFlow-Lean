"""Check remote-only Loogle search without network or a local Lean process."""

from leanflow_cli.lean.lean_search_providers import _loogle_direct_search


def test_remote_lean_never_bootstraps_a_local_loogle_index(monkeypatch, tmp_path):
    from leanflow_cli.cli import loogle_local

    monkeypatch.setenv("TERMINAL_ENV", "ssh")
    monkeypatch.setattr(
        loogle_local,
        "local_loogle_supported",
        lambda: (_ for _ in ()).throw(AssertionError("local probe")),
    )
    assert not loogle_local.local_loogle_needs_build(tmp_path)


def test_loogle_query_keeps_names_types_and_bounded_results(monkeypatch):
    class Response:
        def raise_for_status(self):
            pass

        def json(self):
            return {
                "hits": [
                    None,
                    {
                        "name": "convex_convexHull",
                        "type": "Convex K (convexHull K S)",
                        "module": "Mathlib.Analysis.Convex.Hull",
                    },
                ]
                * 4
            }

    def get(url, **kwargs):
        assert url == "https://loogle.lean-lang.org/json"
        assert kwargs["params"] == {"q": "Convex, convexHull"}
        assert kwargs["timeout"] == 15
        return Response()

    monkeypatch.setattr("httpx.get", get)
    rows, error = _loogle_direct_search("Convex, convexHull", limit=2)
    assert not error and len(rows) == 2
    assert rows[0]["name"] == "convex_convexHull"
    assert "Convex K" in rows[0]["match"]


def test_loogle_error_does_not_look_like_a_search_hit(monkeypatch):
    class Response:
        def raise_for_status(self):
            pass

        def json(self):
            return {"error": "unknown constant"}

    monkeypatch.setattr("httpx.get", lambda *a, **k: Response())
    rows, error = _loogle_direct_search("bad")
    assert rows == [] and error
