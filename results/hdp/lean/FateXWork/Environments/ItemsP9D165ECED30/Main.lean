import Mathlib

theorem convex_combination
    (m n : ℕ)
    (z : Fin m → Fin n → ℝ)
    (coeff : Fin m → ℝ)
    (h_nonneg : ∀ i : Fin m, (0 : ℝ) ≤ coeff i)
    (h_sum : (((∑ i : Fin m, coeff i) : ℝ) = (1 : ℝ))) :
    ∃ x : Fin n → ℝ,
      x = (((∑ i : Fin m, (coeff i) • (z i)) : Fin n → ℝ)) := by
  set_option maxHeartbeats 5000 in
    first | (rfl; done) | (assumption; done) | (simp; done) | (norm_num; done) | (omega; done) | (linarith; done) | (ring; done)
