import Mathlib

/-!
Formalization of the explanatory remark at source label 0.0.5.

The geometric volume comparison is intentionally not formalized here because it
belongs to the preceding theorem, outside this scoped QA slice.
-/

/--
Source proof: the source is an explanatory remark referring to Theorem 0.0.4
and bound (0.2), rather than a standalone proof.
Proof sketch: formalize the explicit analytic consequence using continuity of
`Real.sqrt` at zero, after using the lower bound on vertex counts to ensure
nonnegativity of the logarithmic expression.
Prover notes: `hlog` is the precise Lean rendering of “grows slower than
exponentially”; the polytope and its volume are deliberately outside scope.
-/
theorem high_dimensional_surprise_radius_tendsTo_zero
    (N : ℕ → ℕ)
    (hN : ∀ n, 1 ≤ N n)
    (hlog : Filter.Tendsto (fun n : ℕ => Real.log (N n : ℝ) / (n : ℝ)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n : ℕ => 3 * Real.sqrt (Real.log (N n : ℝ) / (n : ℝ))) Filter.atTop (nhds 0) := by
  sorry
