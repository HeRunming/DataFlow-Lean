import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

noncomputable section

open MeasureTheory

universe u

namespace RandomVectorFormalization

/-- A random vector with `n` real-valued coordinates, represented coordinate-wise. -/
def RandomVector {Ω : Type u} [MeasurableSpace Ω] (X : Ω → Fin n → ℝ) : Prop :=
  ∀ i : Fin n, Measurable (fun ω : Ω => X ω i)

/-- The coordinate-wise expected value of an integrable real-valued random vector. -/
def randomVectorExpectedValue {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → Fin n → ℝ) : Fin n → ℝ :=
  fun i : Fin n => ∫ ω : Ω, X ω i ∂μ

theorem randomVector_expectedValue_coordinatewise
    {Ω : Type u} [MeasurableSpace Ω]
    {n : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → Fin n → ℝ)
    (hX_measurable : RandomVector X)
    (hX_integrable : ∀ i : Fin n, Integrable (fun ω : Ω => X ω i) μ) :
    ∀ i : Fin n,
      randomVectorExpectedValue μ X i = ∫ ω : Ω, X ω i ∂μ := by
  set_option maxHeartbeats 5000 in
    first | (rfl; done) | (assumption; done) | (simp; done) | (norm_num; done) | (omega; done) | (linarith; done) | (ring; done) | (simp_all [RandomVector, randomVectorExpectedValue]; done)

end RandomVectorFormalization
