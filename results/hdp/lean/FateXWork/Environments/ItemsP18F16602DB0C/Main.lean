import Mathlib

def innerProduct {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  ∑ i, x i * y i

noncomputable def norm2 {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, (x i) ^ 2)

theorem cauchy_schwarz (n : ℕ) (x y : Fin n → ℝ) :
    |innerProduct x y| ≤ norm2 x * norm2 y := by
  unfold innerProduct norm2
  calc
    |∑ i, x i * y i| ≤ ∑ i, |x i * y i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ Real.sqrt (∑ i, x i ^ 2) * Real.sqrt (∑ i, y i ^ 2) := by
      simpa [abs_mul, sq_abs] using
        Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => |x i|) (fun i => |y i|)
