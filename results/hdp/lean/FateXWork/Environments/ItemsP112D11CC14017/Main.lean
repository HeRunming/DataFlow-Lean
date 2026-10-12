import Mathlib

/-- The Frobenius norm of a real `m × n` matrix. -/
noncomputable def frobeniusNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  Real.sqrt ((∑ i : Fin m, (∑ j : Fin n, (A i j) ^ (2 : ℕ) : ℝ)) : ℝ)

theorem frobenius_norm_formula {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusNorm A =
      Real.sqrt ((∑ i : Fin m, (∑ j : Fin n, (A i j) ^ (2 : ℕ) : ℝ)) : ℝ) := by
  set_option maxHeartbeats 5000 in
    first | (rfl; done) | (assumption; done) | (simp; done) | (norm_num; done) | (omega; done) | (linarith; done) | (ring; done)
