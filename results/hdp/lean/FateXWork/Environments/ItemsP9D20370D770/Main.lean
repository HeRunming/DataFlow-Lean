import Mathlib

def convexHullRn (n : ℕ) (T : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {x : Fin n → ℝ |
    ∃ (m : ℕ) (z : Fin m → Fin n → ℝ) (coeff : Fin m → ℝ),
      (∀ i : Fin m, z i ∈ T) ∧
      (∀ i : Fin m, (0 : ℝ) ≤ coeff i) ∧
      ((∑ i : Fin m, coeff i) : ℝ) = (1 : ℝ) ∧
      ((∑ i : Fin m, coeff i • z i) : Fin n → ℝ) = x}

theorem mem_convexHullRn_iff (n : ℕ) (T : Set (Fin n → ℝ)) (x : Fin n → ℝ) :
    x ∈ convexHullRn n T ↔
      ∃ (m : ℕ) (z : Fin m → Fin n → ℝ) (coeff : Fin m → ℝ),
        (∀ i : Fin m, z i ∈ T) ∧
        (∀ i : Fin m, (0 : ℝ) ≤ coeff i) ∧
        ((∑ i : Fin m, coeff i) : ℝ) = (1 : ℝ) ∧
        ((∑ i : Fin m, coeff i • z i) : Fin n → ℝ) = x := by
  set_option maxHeartbeats 5000 in
    first | (rfl; done) | (assumption; done) | (simp; done) | (norm_num; done) | (omega; done) | (linarith; done) | (ring; done) | (simp_all [convexHullRn]; done)
