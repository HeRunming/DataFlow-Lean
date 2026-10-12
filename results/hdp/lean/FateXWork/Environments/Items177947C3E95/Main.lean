import Mathlib

/-
Source proof: The supplied source contains no proof text. Prover notes: apply
the library Stirling asymptotic equivalence and unfold `IsEquivalent` into the
quotient formulation of the displayed `1 + o(1)` expression.
-/

/--
Source proof: no proof text is supplied in the source QA excerpt.
Proof sketch: apply the standard Stirling asymptotic and rewrite the main term
as `sqrt (2 * pi * n) * (n / exp 1)^n`.
Prover notes: formalize `1 + o(1)` by convergence of the quotient to `1`
along `atTop`, with `n : ℕ` and all displayed quantities interpreted in `ℝ`.
-/
lemma stirling_approximation :
    Filter.Tendsto
      (fun n : ℕ =>
        (n.factorial : ℝ) /
          (Real.sqrt (2 * Real.pi * (n : ℝ)) *
            (((n : ℝ) / Real.exp 1) ^ n)))
      Filter.atTop (nhds 1) := by
  sorry
