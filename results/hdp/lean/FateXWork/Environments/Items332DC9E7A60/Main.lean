import Mathlib

open MeasureTheory
open ProbabilityTheory

/-- The squared Euclidean norm of a vector indexed by `Fin n`. -/
def euclideanNormSquared (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, (v i : ℝ) ^ (2 : ℕ)

/-- The law of an `n`-dimensional standard Gaussian vector. -/
noncomputable def standardGaussianVectorLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal))

private theorem euclideanNormSquared_eq_sum_sq (n : ℕ) (v : Fin n → ℝ) :
    euclideanNormSquared n v = ∑ i : Fin n, (v i) ^ (2 : ℕ) := by
  rfl

private theorem standard_gaussian_inner_product_distribution_zero
    (v : Fin 0 → ℝ) :
    Measure.map
        (fun z : Fin 0 → ℝ => ∑ i : Fin 0, z i * v i)
        (standardGaussianVectorLaw 0) =
      ProbabilityTheory.gaussianReal 0
        (Real.toNNReal (Real.sqrt (euclideanNormSquared 0 v))) := by
  classical
  simp [standardGaussianVectorLaw, euclideanNormSquared]

private theorem gaussian_inner_product_map_zero (v : Fin 0 → ℝ) :
    Measure.map
        (fun z : Fin 0 → ℝ => (∑ i : Fin 0, z i * v i))
        (Measure.pi fun x => ProbabilityTheory.gaussianReal 0 1) =
      ProbabilityTheory.gaussianReal 0
        (Real.toNNReal (Real.sqrt (∑ i : Fin 0, (v i)^2))) := by
  simp

private theorem fin_sum_univ_succ_mul (n : ℕ) (z v : Fin (n + 1) → ℝ) :
    (∑ i : Fin (n + 1), z i * v i) =
      z 0 * v 0 + ∑ i : Fin n, z i.succ * v i.succ := by
  rw [Fin.sum_univ_succ]

private theorem fin_sum_univ_succ_mul_pointwise
    (n : ℕ) (v : Fin (n + 1) → ℝ) (z : Fin (n + 1) → ℝ) :
    (∑ i : Fin (n + 1), z i * v i) =
      z 0 * v 0 + ∑ i : Fin n, z i.succ * v i.succ := by
  exact fin_sum_univ_succ_mul n z v

private lemma successor_inner_product_head_tail
    (n : ℕ) (v : Fin (n + 1) → ℝ) (z : Fin (n + 1) → ℝ) :
    (∑ i : Fin (n + 1), z i * v i) =
      z 0 * v 0 +
        (∑ i : Fin n, (fun j : Fin n => z j.succ) i * (fun j : Fin n => v j.succ) i) := by
  simpa using fin_sum_univ_succ_mul n z v

private theorem successor_variance_identity
    (n : ℕ) (v : Fin (n + 1) → ℝ) :
    euclideanNormSquared (n + 1) v =
      (v 0) ^ 2 + euclideanNormSquared n (fun i : Fin n => v i.succ) := by
  simp only [euclideanNormSquared, Fin.sum_univ_succ]

private def innerProductCLM (n : ℕ) (v : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  { toFun := fun z => ∑ i : Fin n, z i * v i
    map_add' := by
      intro x y
      simp only [Pi.add_apply, add_mul]
      rw [Finset.sum_add_distrib]
    map_smul' := by
      intro c x
      simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc] }

/-- A linear functional of a standard Gaussian vector is Gaussian with the corresponding variance. -/
theorem standard_gaussian_inner_product_distribution
    (n : ℕ) (v : Fin n → ℝ) :
    Measure.map
        (fun z : Fin n → ℝ =>
          (∑ i : Fin n, (z i : ℝ) * (v i : ℝ)))
        (standardGaussianVectorLaw n) =
      ProbabilityTheory.gaussianReal
        (0 : ℝ)
        (Real.toNNReal (Real.sqrt (euclideanNormSquared n v))) := by sorry
