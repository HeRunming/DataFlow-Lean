import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

theorem equation_2_7 : ∀ x : ℝ, Real.cosh x ≤ Real.exp (x ^ 2 / (2 : ℝ)) := by
  intro x
  exact Real.cosh_le_exp_half_sq x
