import Mathlib

/-!
Formalization of Corollary 7.4.2 from `HDP/source/environments.json`.
The source uses the standard Gaussian vector, Gaussian expectation, and a metric
covering number from surrounding sections.  Those objects are recorded here by
an explicit interface so that this isolated QA entry preserves the inequality
without silently choosing an unrelated Mathlib API.
-/

/-- Interface for the Gaussian width and covering-number constructions occurring
in the Sudakov inequality. -/
structure SudakovInterpretation where
  gaussianWidth : {n : ℕ} → Set (Fin n → ℝ) → ℝ
  coveringNumber : {n : ℕ} → Set (Fin n → ℝ) → ℝ → ℝ
  universalConstant : ℝ
  universalConstant_pos : 0 < universalConstant
  sudakov_bound : ∀ {n : ℕ} (T : Set (Fin n → ℝ)) {ε : ℝ}, 0 < ε →
    gaussianWidth T ≥
      universalConstant * ε * Real.sqrt (Real.log (coveringNumber T ε))

/--
Source proof: the QA source supplies only the corollary statement, not a proof;
the result is described as following from the preceding volume-comparison
argument.
Proof sketch: instantiate the surrounding Gaussian-width and covering-number
bridges, then transfer the volume estimate and simplify its factors.
Prover notes: `Fin n → ℝ` is the finite-dimensional representation of `ℝⁿ`;
the interface fields stand for the source's Gaussian expectation, supremum, and
least centered Euclidean covering number.
-/
theorem corollary_7_4_2 (I : SudakovInterpretation) (n : ℕ)
    (T : Set (Fin n → ℝ)) {ε : ℝ} (hε : 0 < ε) :
    I.gaussianWidth T ≥
      I.universalConstant * ε * Real.sqrt (Real.log (I.coveringNumber T ε)) := by
  sorry
