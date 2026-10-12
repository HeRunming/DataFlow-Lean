import Mathlib

theorem stirling_nonasymptotic :
    ∀ n : ℕ,
      Real.sqrt ((2 : ℝ) * Real.pi * (n : ℝ)) *
          ((n : ℝ) / Real.exp (1 : ℝ)) ^ n *
          Real.exp ((1 : ℝ) / ((12 : ℝ) * (n : ℝ) + 1)) ≤
        ((Nat.factorial n : ℕ) : ℝ) ∧
      ((Nat.factorial n : ℕ) : ℝ) ≤
        Real.sqrt ((2 : ℝ) * Real.pi * (n : ℝ)) *
          ((n : ℝ) / Real.exp (1 : ℝ)) ^ n *
          Real.exp ((1 : ℝ) / ((12 : ℝ) * (n : ℝ))) := by
  sorry
