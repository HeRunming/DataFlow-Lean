import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Order.Interval.Finset.Nat

/-- The vertex set `{1, ..., n}`. -/
abbrev LabeledVertex (n : ℕ) := ↥(Finset.Icc 1 n)

/-- A finite simple undirected graph whose vertices are labeled by `{1, ..., n}`. -/
abbrev FiniteSimpleGraph (n : ℕ) := SimpleGraph (LabeledVertex n)

/-- The edges of a finite simple graph form a set of unordered pairs of vertices. -/
theorem FiniteSimpleGraph.exists_edge_set (n : ℕ) (G : FiniteSimpleGraph n) :
    ∃ E : Set (Sym2 (LabeledVertex n)), E = G.edgeSet := by
  exact ⟨G.edgeSet, rfl⟩
