import Mathlib

open MeasureTheory

universe u

namespace SecondMoment

/-- The uncentered second moment matrix, defined when all entrywise
products have finite expectations. -/
noncomputable def secondMomentMatrix
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (X : Ω → Fin n → ℝ)
    (_hX : ∀ (i j : Fin n),
      Integrable (fun ω : Ω => X ω i * X ω j) μ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun (i j : Fin n) => ∫ ω : Ω, X ω i * X ω j ∂μ

/-- Entrywise formulation of Σ(X) = E[XXᵀ]. -/
theorem secondMomentMatrix_entry
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (X : Ω → Fin n → ℝ)
    (hX : ∀ (i j : Fin n),
      Integrable (fun ω : Ω => X ω i * X ω j) μ)
    (i j : Fin n) :
    secondMomentMatrix μ X hX i j =
      ∫ ω : Ω, X ω i * X ω j ∂μ := by
  set_option maxHeartbeats 5000 in
    first | (rfl; done) | (assumption; done) | (simp; done) | (norm_num; done) | (omega; done) | (linarith; done) | (ring; done)

end SecondMoment
