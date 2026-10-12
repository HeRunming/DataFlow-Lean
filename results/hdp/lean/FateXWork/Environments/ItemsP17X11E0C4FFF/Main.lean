import Mathlib

noncomputable def euclideanNorm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, x i ^ 2)

theorem euclideanNorm_sq_eq_dotProduct_self {n : ℕ} (x : Fin n → ℝ) :
    euclideanNorm x ^ 2 = dotProduct x x := by
  rw [euclideanNorm, Real.sq_sqrt (by positivity)]; simp [dotProduct, pow_two]
