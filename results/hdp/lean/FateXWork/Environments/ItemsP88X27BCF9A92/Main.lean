import Mathlib

open scoped BigOperators

theorem semidefinite_relaxation_maximum
    (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j : Fin n, A i j = A j i) :
    ∃ M : ℝ,
      ∃ X : Fin n → EuclideanSpace ℝ (Fin n),
        (∀ i : Fin n, ‖X i‖ = (1 : ℝ)) ∧
          ((∑ i : Fin n,
              ((∑ j : Fin n,
                  (A i j * inner ℝ (X i) (X j) : ℝ)) : ℝ)) : ℝ) = M ∧
            ∀ Y : Fin n → EuclideanSpace ℝ (Fin n),
              (∀ i : Fin n, ‖Y i‖ = (1 : ℝ)) →
                ((∑ i : Fin n,
                    ((∑ j : Fin n,
                        (A i j * inner ℝ (Y i) (Y j) : ℝ)) : ℝ)) : ℝ) ≤ M := by
  sorry
