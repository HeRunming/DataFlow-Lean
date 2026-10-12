import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Data.Real.Basic

theorem adjacency_matrix_spec
    (n : ℕ)
    (G : SimpleGraph (Fin n)) :
    letI : DecidableRel G.Adj := Classical.decRel G.Adj
    let A : Matrix (Fin n) (Fin n) ℝ := SimpleGraph.adjMatrix ℝ G
    A.IsSymm ∧
      ∀ (i j : Fin n),
        A i j = if G.Adj i j then (1 : ℝ) else (0 : ℝ) := by
  dsimp
  constructor
  · ext i j
    by_cases h : G.Adj i j
    · have h' : G.Adj j i := (G.adj_comm i j).mp h
      simp [h, h']
    · have h' : ¬ G.Adj j i := by
        intro hji
        exact h ((G.adj_comm j i).mp hji)
      simp [h, h']
  · intro i j
    rfl
