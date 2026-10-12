import Mathlib

open MeasureTheory
open ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

 theorem variance_mean_square_identity
    (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Z : Ω → ℝ)
    (mu : ℝ)
    (hZ : Measurable Z)
    (hZ2 : MemLp Z (2 : ℕ) P)
    (hmu : mu = ((∫ ω : Ω, Z ω ∂P) : ℝ)) :
    variance Z P = ((∫ ω : Ω, (Z ω - mu) ^ (2 : ℕ) ∂P) : ℝ) ∧
      ((∫ ω : Ω, (Z ω - mu) ^ (2 : ℕ) ∂P) : ℝ) =
        ((∫ ω : Ω, (Z ω) ^ (2 : ℕ) ∂P) : ℝ) - mu ^ (2 : ℕ) := by
  subst mu
  have h₁ : variance Z P = ((∫ ω : Ω, (Z ω - (∫ x, Z x ∂P)) ^ (2 : ℕ) ∂P) : ℝ) :=
    variance_eq_integral hZ.aemeasurable
  have h₂ : variance Z P = ((∫ ω : Ω, (Z ω) ^ (2 : ℕ) ∂P) : ℝ) -
      (∫ ω : Ω, Z ω ∂P) ^ (2 : ℕ) := variance_eq_sub hZ2
  constructor
  · exact h₁
  · linarith [h₁, h₂]
