import Mathlib

/-!
# Centering and the L² norm

Formalization of scoped source item `p50.f1`, equation (2.23).
-/

namespace FateXWork.Environments.ItemsP50F13409CB4F

open MeasureTheory

/--
Centering a real-valued random variable on a probability space cannot increase its
extended `L²` seminorm.

Source proof: This follows from the extremal property of the variance (Exercise 0.2).
Proof sketch: the mean is the best constant `L²` approximation; expand the square around
that mean, use that the integral of the centered function vanishes, and compare with the
constant zero. Prover notes: search for the `snorm`-at-two integral characterization and
variance/mean minimization lemmas.
-/
theorem centeredL2Norm_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) :
    eLpNorm (fun ω => X ω - ∫ x, X x ∂μ) 2 μ ≤ eLpNorm X 2 μ := by
  sorry

end FateXWork.Environments.ItemsP50F13409CB4F
