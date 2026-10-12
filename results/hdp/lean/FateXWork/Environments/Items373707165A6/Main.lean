import Mathlib

namespace SourceTensor

def tensorPower (n k : ℕ) (u : Fin n → ℝ) : (Fin k → Fin n) → ℝ :=
  fun indices => ∏ j : Fin k, (u (indices j) : ℝ)

def tensorPowerTwo (n : ℕ) (u : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => u i * u j

theorem tensorPower_coordinate_formula (n k : ℕ) (u : Fin n → ℝ) :
    ∀ indices : Fin k → Fin n,
      tensorPower n k u indices =
        (∏ j : Fin k, (u (indices j) : ℝ)) := by
  set_option maxHeartbeats 5000 in
    first | (rfl; done) | (assumption; done) | (simp; done) | (norm_num; done) | (omega; done) | (linarith; done) | (ring; done) | (simp_all [tensorPower, tensorPowerTwo]; done)

theorem tensorPower_two_coordinate_formula (n : ℕ) (u : Fin n → ℝ) :
    ∀ i : Fin n, ∀ j : Fin n,
      tensorPowerTwo n u i j = u i * u j := by
  set_option maxHeartbeats 5000 in
    first | (rfl; done) | (assumption; done) | (simp; done) | (norm_num; done) | (omega; done) | (linarith; done) | (ring; done) | (simp_all [tensorPower, tensorPowerTwo]; done)

theorem tensorPower_two_matrix_formula (n : ℕ) (u : Fin n → ℝ) :
    tensorPowerTwo n u = Matrix.vecMulVec u u := by
  set_option maxHeartbeats 5000 in
    first | (rfl; done) | (assumption; done) | (simp; done) | (norm_num; done) | (omega; done) | (linarith; done) | (ring; done) | (simp_all [tensorPower, tensorPowerTwo]; done)

end SourceTensor
