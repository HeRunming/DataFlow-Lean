import Mathlib

open MeasureTheory

namespace Source

/-- A measurable random vector on a probability space is isotropic when its
entrywise second moments exist and its second-moment matrix is the identity. -/
def IsIsotropic
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin n → ℝ) : Prop :=
  Measurable X ∧
    (∀ (i j : Fin n),
      Integrable (fun ω : Ω => X ω i * X ω j) μ) ∧
    ((fun (i j : Fin n) =>
        ∫ ω : Ω, X ω i * X ω j ∂μ) : Matrix (Fin n) (Fin n) ℝ) =
      (1 : Matrix (Fin n) (Fin n) ℝ)

/-- On the domain of measurable random vectors with finite second moments,
isotropy is exactly the stated second-moment matrix identity. -/
theorem isIsotropic_iff_secondMoment_eq_identity
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin n → ℝ)
    (hX : Measurable X)
    (hMoments : ∀ (i j : Fin n),
      Integrable (fun ω : Ω => X ω i * X ω j) μ) :
    IsIsotropic μ X ↔
      ((fun (i j : Fin n) =>
          ∫ ω : Ω, X ω i * X ω j ∂μ) : Matrix (Fin n) (Fin n) ℝ) =
        (1 : Matrix (Fin n) (Fin n) ℝ) := by sorry

end Source
