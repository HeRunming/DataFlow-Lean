import Mathlib

namespace SourceComparison

/-- Comparison relative to fixed absolute constants, supplied independently
of the quantities being compared. -/
def ComparableWith (c₁ c₂ : ℝ) (a b : ℝ) : Prop :=
  (0 : ℝ) < c₁ ∧ (0 : ℝ) < c₂ ∧ c₁ * b ≤ a ∧ a ≤ c₂ * b

/-- The meaning of the source's comparison notation for fixed constants. -/
theorem comparableWith_iff (c₁ c₂ : ℝ) (a b : ℝ) :
    ComparableWith c₁ c₂ a b ↔
      (0 : ℝ) < c₁ ∧ (0 : ℝ) < c₂ ∧ c₁ * b ≤ a ∧ a ≤ c₂ * b := by sorry

end SourceComparison
