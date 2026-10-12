import Mathlib

open scoped BigOperators

namespace OrthogonalGaussian

/-- The standard Gaussian law, characterized by all real linear projections. -/
def HasStandardNormalLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (n : ℕ)
    (Z : Ω → Fin n → ℝ) : Prop :=
  ∀ (coeff : Fin n → ℝ),
    ProbabilityTheory.HasLaw
      (fun ω => (∑ i : Fin n, coeff i * Z ω i : ℝ))
      (ProbabilityTheory.gaussianReal (0 : ℝ)
        (Real.toNNReal (∑ i : Fin n, (coeff i) ^ 2 : ℝ)))
      P

/-- Column orthonormality for a square real matrix. -/
def IsOrthogonalMatrix (n : ℕ) (U : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ (i j : Fin n),
    (∑ k : Fin n, U k i * U k j : ℝ) =
      (if i = j then (1 : ℝ) else (0 : ℝ))

theorem orthogonal_transform_hasStandardNormalLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (n : ℕ)
    (Z : Ω → Fin n → ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ)
    (hU : IsOrthogonalMatrix n U)
    (hZ : HasStandardNormalLaw P n Z) :
    HasStandardNormalLaw P n
      (fun ω (i : Fin n) => (∑ j : Fin n, U i j * Z ω j : ℝ)) := by
  classical
  intro coeff
  let coeff' : Fin n → ℝ := fun j => ∑ i : Fin n, coeff i * U i j
  have hleft : Matrix.transpose U * U = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
    exact hU i j
  letI : Invertible U := invertibleOfLeftInverse U (Matrix.transpose U) hleft
  have hright : U * Matrix.transpose U = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    have hi : U⁻¹ = Matrix.transpose U := Matrix.inv_eq_left_inv hleft
    rw [← hi]
    exact Matrix.mul_inv_of_invertible U
  have hrow (i k : Fin n) : (∑ j : Fin n, U i j * U k j : ℝ) = if i = k then 1 else 0 := by
    have h := congrArg (fun M => M i k) hright
    simpa [Matrix.mul_apply, Matrix.transpose_apply] using h
  have hdiag (i : Fin n) : (∑ k : Fin n, coeff i * coeff k * (if i = k then 1 else 0)) = coeff i ^ 2 := by
    rw [Finset.sum_eq_single i]
    · simp [pow_two]
    · intro k hk hki
      simp [Ne.symm hki]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  have hnorm : (∑ j : Fin n, coeff' j ^ 2 : ℝ) = ∑ i : Fin n, coeff i ^ 2 := by
    simp only [coeff']
    calc
      (∑ j : Fin n, (∑ i : Fin n, coeff i * U i j) ^ 2 : ℝ) =
          ∑ j : Fin n, ∑ i : Fin n, ∑ k : Fin n, coeff i * coeff k * (U i j * U k j) := by
            simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro k hk
            ring
      _ = ∑ i : Fin n, ∑ k : Fin n, coeff i * coeff k * (∑ j : Fin n, U i j * U k j) := by
            calc
              _ = ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, coeff i * coeff k * (U i j * U k j) := by
                    rw [Finset.sum_comm]
              _ = ∑ i : Fin n, ∑ k : Fin n, ∑ j : Fin n, coeff i * coeff k * (U i j * U k j) := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    rw [Finset.sum_comm]
              _ = ∑ i : Fin n, ∑ k : Fin n, coeff i * coeff k * (∑ j : Fin n, U i j * U k j) := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    apply Finset.sum_congr rfl
                    intro k hk
                    rw [Finset.mul_sum]
      _ = ∑ i : Fin n, coeff i ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            calc
              (∑ k : Fin n, coeff i * coeff k * (∑ j : Fin n, U i j * U k j)) =
                  ∑ k : Fin n, coeff i * coeff k * (if i = k then 1 else 0) := by
                    apply Finset.sum_congr rfl
                    intro k hk
                    rw [hrow i k]
              _ = coeff i ^ 2 := hdiag i
  have hproj (ω : Ω) :
      (∑ i : Fin n, coeff i * (∑ j : Fin n, U i j * Z ω j : ℝ) : ℝ) =
        ∑ j : Fin n, coeff' j * Z ω j := by
    simp only [coeff']
    calc
      (∑ i : Fin n, coeff i * ∑ j : Fin n, U i j * Z ω j : ℝ) =
          ∑ i : Fin n, ∑ j : Fin n, coeff i * (U i j * Z ω j) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
      _ = ∑ j : Fin n, ∑ i : Fin n, coeff i * (U i j * Z ω j) := Finset.sum_comm
      _ = ∑ j : Fin n, (∑ i : Fin n, coeff i * U i j) * Z ω j := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i hi
            ring
  have h := hZ coeff'
  change ProbabilityTheory.HasLaw
    (fun ω => ∑ i : Fin n, coeff i * (∑ j : Fin n, U i j * Z ω j : ℝ))
    (ProbabilityTheory.gaussianReal 0 (∑ i : Fin n, coeff i ^ 2).toNNReal) P
  rw [← hnorm]
  convert h using 1
  funext ω
  exact hproj ω

end OrthogonalGaussian
