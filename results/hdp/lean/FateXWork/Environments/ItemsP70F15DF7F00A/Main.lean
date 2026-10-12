import Mathlib

open MeasureTheory
open ProbabilityTheory

noncomputable def covMatrix {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (X : Ω → Fin n → ℝ) (μ : Measure Ω) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    ProbabilityTheory.covariance (fun ω : Ω => X ω i) (fun ω : Ω => X ω j) μ

theorem covariance_eq_centered_product
    {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (f g : Ω → ℝ) :
    ProbabilityTheory.covariance f g μ =
      ∫ ω : Ω,
        (f ω - (∫ ω' : Ω, f ω' ∂μ)) *
          (g ω - (∫ ω' : Ω, g ω' ∂μ)) ∂μ := by
  simp [ProbabilityTheory.covariance]

theorem covMatrix_entry_eq_coordinate_covariance
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → Fin n → ℝ)
    (hX : ∀ i : Fin n, MemLp (fun ω : Ω => X ω i) 2 μ) :
    ∀ i j : Fin n,
      covMatrix X μ i j =
        ∫ ω : Ω,
          ((X ω i) - (∫ ω' : Ω, X ω' i ∂μ)) *
            ((X ω j) - (∫ ω' : Ω, X ω' j ∂μ)) ∂μ := by
  intro i j
  exact covariance_eq_centered_product (fun ω : Ω => X ω i) (fun ω : Ω => X ω j)
