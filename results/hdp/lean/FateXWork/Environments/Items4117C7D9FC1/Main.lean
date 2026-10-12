import Mathlib

open scoped BigOperators

/-- A finite family of real vectors is orthonormal when its members have unit norm
and distinct members are orthogonal. -/
def SourceOrthonormalFamily {d r : ℕ} (family : Fin r → Fin d → ℝ) : Prop :=
  (∀ i : Fin r, ((∑ a : Fin d, (family i a) ^ 2) : ℝ) = 1) ∧
    (∀ i j : Fin r, i ≠ j → ((∑ a : Fin d, family i a * family j a) : ℝ) = 0)

theorem real_matrix_singular_value_decomposition
    (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ r : ℕ, ∃ s : Fin r → ℝ, ∃ u : Fin r → Fin m → ℝ,
      ∃ v : Fin r → Fin n → ℝ,
        r = min m n ∧
          (∀ i : Fin r, 0 ≤ s i) ∧
          SourceOrthonormalFamily u ∧
          SourceOrthonormalFamily v ∧
          A =
            ((∑ i : Fin r,
                fun a b => s i * u i a * v i b) : Matrix (Fin m) (Fin n) ℝ) := by
  sorry
