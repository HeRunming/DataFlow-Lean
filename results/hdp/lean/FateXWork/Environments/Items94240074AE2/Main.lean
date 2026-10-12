import Mathlib

 def LinearRegressionModel
    (m n : ℕ)
    (X : Matrix (Fin m) (Fin n) ℝ)
    (Y : Fin m → ℝ)
    (theta : Fin n → ℝ)
    (w : Fin m → ℝ) : Prop :=
  Y = Matrix.mulVec X theta + w

theorem linearRegressionModel_spec
    (m n : ℕ)
    (X : Matrix (Fin m) (Fin n) ℝ)
    (Y : Fin m → ℝ)
    (theta : Fin n → ℝ)
    (w : Fin m → ℝ) :
    LinearRegressionModel m n X Y theta w ↔
      Y = Matrix.mulVec X theta + w := by
  set_option maxHeartbeats 5000 in
    first | (rfl; done) | (assumption; done) | (simp; done) | (norm_num; done) | (omega; done) | (linarith; done) | (ring; done) | (simp_all [LinearRegressionModel]; done)
