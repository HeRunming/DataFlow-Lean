import Mathlib

/-!
Formalization interface for HDP Exercise 3.6, the expected `ℓ^p` norm of a
standard Gaussian vector.

The source uses `p ∈ [1, ∞]`, while Lean's real numbers do not contain the
endpoint `∞`. The two finite-real regimes below retain the stated inequalities;
the endpoint is recorded as a scope change in the adjacent blueprint.
-/

namespace FateXWork.Environments.Items3684DAE4B5

noncomputable section

/-- The lower-bound profile appearing in Exercise 3.6. -/
def gaussianLpLowerProfile (n : ℕ) (p : ℝ) : ℝ :=
  if p ≤ Real.log n then Real.sqrt p * n ^ (1 / p) else Real.sqrt (Real.log n)

/--
Source proof: the exercise supplies no proof text. Prover notes: for
`p ≤ log n`, compare the expected `ℓ^p` norm with Gaussian moments, using
`(𝔼 |g|^p)^(1/p) ≍ √p`; for `log n ≤ p`, compare with the maximum coordinate
and use the standard lower bound `𝔼 max_i |g_i| ≳ √(log n)`.

This is a deliberately partial representation bridge. `expectedLpNorm n p`
stands for `𝔼 ‖X‖ₚ` for an `n`-dimensional vector with independent standard
Gaussian coordinates; constructing that random vector and identifying this
functional with a measure-theoretic expectation are not encoded here.
-/
theorem expected_lpNorm_standardGaussian_lower_bound
    (expectedLpNorm : ℕ → ℝ → ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n → ∀ p : ℝ, 1 ≤ p →
      c * gaussianLpLowerProfile n p ≤ expectedLpNorm n p := by
  sorry

end

end FateXWork.Environments.Items3684DAE4B5
