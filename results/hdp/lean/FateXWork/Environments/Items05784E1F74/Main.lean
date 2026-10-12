import Mathlib

/-!
Formalization of HDP exercise 0.5.
-/

/--
Source proof: The exercise asks for the standard simplex example (the vertices of the
simplex, with its barycenter as `x`); no proof text is supplied in the source QA.
Proof sketch: choose the `n` coordinate vertices and their barycenter, then minimize
squared Euclidean distance under nonnegative coefficients summing to one and supported
on at most `k` vertices. The minimum is `1/k - 1/n`.
Prover notes: the statement keeps the finite-dimensional representation explicit. The
convex-combination predicate is expressed using `Fin k`-indexed points and weights;
positivity of `n` and `k` avoids division by zero.
-/
theorem approximate_caratheodory_asymptotically_tight :
    ∀ n : ℕ, 0 < n → ∃ T : Set (EuclideanSpace ℝ (Fin n)), ∃ x : EuclideanSpace ℝ (Fin n),
      x ∈ convexHull ℝ T ∧
      ∀ k : ℕ, 0 < k →
        ∀ (w : Fin k → ℝ) (xj : Fin k → EuclideanSpace ℝ (Fin n)),
          (∀ j, 0 ≤ w j) →
          (∑ j, w j) = 1 →
          (∀ j, xj j ∈ T) →
          ‖x - ∑ j, w j • xj j‖ ≥
            Real.sqrt ((1 : ℝ) / k - (1 : ℝ) / n) := by
  sorry

/--
Source proof: The source gives no proof text for the concluding asymptotic
observation. Proof sketch: for fixed positive `k`, the radicand tends to
`1 / k` as `n` tends to infinity, and continuity of `Real.sqrt` gives the
stated limit. Prover notes: this is the precise companion statement for the
source's instruction to let the dimension grow while keeping `k` fixed.
-/
theorem approximate_caratheodory_bound_tends_to_fixed_k_limit
    (k : ℕ) (hk : 0 < k) :
    Filter.Tendsto (fun n : ℕ => Real.sqrt ((1 : ℝ) / k - (1 : ℝ) / n))
      atTop (nhds (Real.sqrt ((1 : ℝ) / k))) := by
  sorry
