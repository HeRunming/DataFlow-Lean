import Mathlib

open scoped BigOperators

namespace TensorArraySource

/-- A real tensor with one finite coordinate index for each axis. -/
abbrev Tensor (k : ℕ) (n : Fin k → ℕ) :=
  ((j : Fin k) → Fin (n j)) → ℝ

/-- The canonical inner product, defined by the source's coordinate sum. -/
noncomputable def canonicalInner {k : ℕ} {n : Fin k → ℕ}
    (A B : Tensor k n) : ℝ :=
  (∑ idx : ((j : Fin k) → Fin (n j)), (A idx * B idx : ℝ) : ℝ)

/-- Equation (3.36). -/
theorem canonicalInner_eq_sum (k : ℕ) (n : Fin k → ℕ)
    (A B : Tensor k n) :
    canonicalInner A B =
      (∑ idx : ((j : Fin k) → Fin (n j)), (A idx * B idx : ℝ) : ℝ) := by
  set_option maxHeartbeats 5000 in
    first | (rfl; done) | (assumption; done) | (simp; done) | (norm_num; done) | (omega; done) | (linarith; done) | (ring; done) | (simp_all [Tensor]; done)

end TensorArraySource
