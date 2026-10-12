import Mathlib

open MeasureTheory

def IsotropicRandomVector {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (μ : Measure Ω)
    (X : Ω → EuclideanSpace ℝ (Fin n)) : Prop :=
  IsProbabilityMeasure μ ∧
    AEStronglyMeasurable X μ ∧
    Integrable X μ ∧
    ∀ i j : Fin n,
      ∫ ω : Ω, (X ω) i * (X ω) j ∂μ =
        if i = j then (1 : ℝ) else (0 : ℝ)

private lemma isotropic_coordinate_square_integrable
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (μ : Measure Ω)
    (X : Ω → EuclideanSpace ℝ (Fin n)) (hX : IsotropicRandomVector μ X)
    (i : Fin n) : Integrable (fun ω => X ω i * X ω i) μ := by
  by_contra h
  have hzero := integral_undef h
  have hone := hX.2.2.2 i i
  simp only [if_pos rfl] at hone
  rw [hzero] at hone
  norm_num at hone

theorem isotropic_mean_norm_le_one
    (n : ℕ) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (X : Ω → EuclideanSpace ℝ (Fin n))
    (hX : IsotropicRandomVector μ X) :
    ‖∫ ω : Ω, X ω ∂μ‖ ≤ (1 : ℝ) := by
  have hnorm := norm_integral_le_integral_norm (μ := μ) X
  sorry

theorem exists_isotropic_mean_norm_one_positive
    (n : ℕ) (hn : 0 < n) :
    ∃ μ : Measure (EuclideanSpace ℝ (Fin n)),
      IsotropicRandomVector μ
          (fun x : EuclideanSpace ℝ (Fin n) => x) ∧
        ‖∫ x : EuclideanSpace ℝ (Fin n), x ∂μ‖ = (1 : ℝ) := by
  sorry

theorem zero_dimensional_mean_norm_ne_one
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (X : Ω → EuclideanSpace ℝ (Fin 0))
    (hX : IsotropicRandomVector μ X) :
    ‖∫ ω : Ω, X ω ∂μ‖ ≠ (1 : ℝ) := by
  sorry
