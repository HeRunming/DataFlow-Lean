import Mathlib

/-!
# Gaussian tails

This file records a density-integral formalization of Proposition 2.1.2.
-/

/-- The density of the standard Gaussian at `x`. -/
noncomputable def standardGaussianDensity (x : ℝ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(x ^ 2) / 2)

/-- The upper tail represented as the integral of the standard Gaussian density.

This is the analytic representation used for the draft; identifying it with the
probability of `{g ≥ t}` for `g ~ N(0,1)` is recorded as a source-fidelity bridge
in the blueprint and remains outside this initial statement skeleton.
-/
noncomputable def standardGaussianTail (t : ℝ) : ℝ :=
  ∫ x in Set.Ioi t, standardGaussianDensity x

/--
Source proof: the standard Gaussian tail bounds (Mills' inequalities) are
obtained by integrating the Gaussian density and comparing the integrand with
its derivative; the source excerpt supplies the statement but no proof text.
Proof sketch: prove the lower and upper Mills bounds for the density integral,
then derive the `t ≥ 1` consequence from `1 / t ≤ 1`.
Prover notes: the source uses probability for a standard normal random variable;
this draft uses the equivalent density-tail integral and records that
representation change in `Blueprint.md`.
-/
theorem gaussian_tails (t : ℝ) (ht : 0 < t) :
    (t / (t ^ 2 + 1)) * standardGaussianDensity t ≤ standardGaussianTail t ∧
      standardGaussianTail t ≤ (1 / t) * standardGaussianDensity t ∧
      (1 ≤ t → standardGaussianTail t ≤ standardGaussianDensity t) := by
  sorry
