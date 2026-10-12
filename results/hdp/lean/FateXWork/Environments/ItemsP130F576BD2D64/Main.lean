import Mathlib

/--
Source proof (HDP/source/environments.json:456): multiply the normalized
sign-stability estimate by `√n`, using that both eigenvectors are `√n` times
the corresponding unit vectors.
Prover notes: use `norm_smul` and positivity of `n` and `μ` to scale the bound.
-/
lemma normalized_to_unnormalized_distance
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : ℕ} {μ C : ℝ} {θ : ℝ} {xD xA vD vA : V}
    (hn : 0 < n) (hμ : 0 < μ) (hC : 0 ≤ C)
    (hvD : vD = (Real.sqrt n) • xD)
    (hvA : vA = (Real.sqrt n) • xA)
    (hθ : θ = 1 ∨ θ = -1)
    (hbound : ‖xD - θ • xA‖ ≤ C / (μ * Real.sqrt n)) :
    ‖vD - θ • vA‖ ≤ C / μ := by
  sorry

/--
Source proof (HDP/source/environments.json:456): Exercise 4.16 gives a sign
`θ ∈ {-1,1}` for which the normalized second eigenvectors are close, and the
known eigenvectors have norm `√n`; scaling yields the unnormalized estimate.
Prover notes: the sine/angle argument is represented by `hbound`, the
upstream normalized estimate. Apply `normalized_to_unnormalized_distance`.
The matrix/eigenvector origins are abstracted by the explicit scaling
hypotheses because the source excerpt does not define those objects.
-/
theorem p130_f5_eigenvector_sign_stability
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : ℕ} {μ C : ℝ} {xD xA vD vA : V}
    (hn : 0 < n) (hμ : 0 < μ) (hC : 0 ≤ C)
    (hvD : vD = (Real.sqrt n) • xD)
    (hvA : vA = (Real.sqrt n) • xA)
    (hbound : ∃ θ : ℝ, (θ = 1 ∨ θ = -1) ∧
      ‖xD - θ • xA‖ ≤ C / (μ * Real.sqrt n)) :
    ∃ θ : ℝ, (θ = 1 ∨ θ = -1) ∧ ‖vD - θ • vA‖ ≤ C / μ := by
  sorry
