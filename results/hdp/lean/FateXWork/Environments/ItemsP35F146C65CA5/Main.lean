import Mathlib

/-!
Formalization of source item `p35.f1` from `HDP/source/environments.json`.
-/

noncomputable def fairCoinHalfProbability (N : ℕ) : ℝ :=
  if Even N then (Nat.choose N (N / 2) : ℝ) / (2 : ℝ) ^ N else 0

/--
Source proof: count the flip sequences with exactly `N / 2` heads; there are
`Nat.choose N (N / 2)` such sequences, each of probability `2⁻ᴺ`.
Prover notes: unfold the definition and simplify under the evenness hypothesis.
-/
theorem fairCoinHalfProbability_eq_centralBinomial {N : ℕ} (hN : Even N) :
    fairCoinHalfProbability N = (Nat.choose N (N / 2) : ℝ) / (2 : ℝ) ^ N := by
  sorry
