import Mathlib

namespace RandomGraph

def expectedDegree (n : ℕ) (p : ℝ) (v : Fin n) : ℝ :=
  ∑ u : Fin n, if u = v then (0 : ℝ) else p

theorem expected_degree_Gnp (n : ℕ) (p : ℝ)
    (hp0 : (0 : ℝ) ≤ p) (hp1 : p ≤ (1 : ℝ)) :
    ∀ v : Fin n,
      let d : ℝ := ((n : ℝ) - (1 : ℝ)) * p
      expectedDegree n p v = d := by
  sorry

end RandomGraph
