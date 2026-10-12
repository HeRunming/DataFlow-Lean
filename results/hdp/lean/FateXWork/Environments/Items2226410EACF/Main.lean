import Mathlib

open MeasureTheory

noncomputable section

namespace GaussianMoments

/-- Density of the standard normal law with respect to Lebesgue measure. -/
def standardNormalDensity (x : ℝ) : ℝ :=
  Real.exp (-(x ^ (2 : ℕ)) / (2 : ℝ)) /
    Real.sqrt ((2 : ℝ) * Real.pi)

/-- Expectation under the standard normal law. -/
def gaussianExpectation (f : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ, f x * standardNormalDensity x

/-- The absolute moment with real exponent `p`. -/
def gaussianAbsoluteMoment (p : ℝ) : ℝ :=
  gaussianExpectation (fun x : ℝ => Real.rpow |x| p)

/-- The source-defined finite-exponent Lp norm, used for `p ≥ 1`. -/
def gaussianLpNorm (p : ℝ) : ℝ :=
  Real.rpow (gaussianAbsoluteMoment p) ((1 : ℝ) / p)

/-- Part (a): the absolute moments of a standard normal variable. -/
theorem absolute_moment_standard_normal
    (p : ℝ) (hp : (1 : ℝ) ≤ p) :
    gaussianAbsoluteMoment p =
      Real.rpow (2 : ℝ) (p / (2 : ℝ)) / Real.sqrt Real.pi *
        Real.Gamma ((p + (1 : ℝ)) / (2 : ℝ)) := by sorry

/-- Part (b): the moment expression and the asymptotic of the Lp norm. -/
theorem lp_norm_standard_normal :
    (∀ (p : ℝ), (1 : ℝ) ≤ p →
      gaussianLpNorm p =
        Real.rpow (gaussianAbsoluteMoment p) ((1 : ℝ) / p)) ∧
    Asymptotics.IsEquivalent Filter.atTop
      (fun p : ℝ => gaussianLpNorm p)
      (fun p : ℝ => Real.sqrt (p / Real.exp (1 : ℝ))) := by sorry

end GaussianMoments
