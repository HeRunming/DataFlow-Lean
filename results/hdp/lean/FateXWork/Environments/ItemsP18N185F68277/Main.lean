import Mathlib.Data.Real.ConjExponents

theorem one_zero_and_top_conjugate :
    (1 : ENNReal) / (0 : ENNReal) = ⊤ ∧
    (1 : ENNReal) / ⊤ = (0 : ENNReal) ∧
    ENNReal.HolderConjugate (1 : ENNReal) ⊤ ∧
    ENNReal.HolderConjugate ⊤ (1 : ENNReal) := by
  sorry
