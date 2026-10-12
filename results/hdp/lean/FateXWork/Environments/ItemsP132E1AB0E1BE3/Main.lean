import Mathlib.Data.Nat.Choose.Sum

/-- Equation (4.27) implies the lower bound (4.26), using (4.15). -/
theorem equation_4_27_implies_equation_4_26
    (catalan : ℕ → ℚ)
    (h427 : ∀ n : ℕ, catalan n = ((2 * n).choose n : ℚ) / (n + 1 : ℚ)) :
    ∀ n : ℕ,
      (4 : ℚ) ^ n / (((2 * n + 1) * (n + 1) : ℕ) : ℚ) ≤ catalan n := by
  intro n
  have hb : 4 ^ n ≤ (2 * n + 1) * (2 * n).choose n := by
    calc
      4 ^ n = 2 ^ (2 * n) := by rw [pow_mul]; rfl
      _ = ∑ k ∈ Finset.range (2 * n + 1), (2 * n).choose k := (Nat.sum_range_choose (2 * n)).symm
      _ ≤ ∑ k ∈ Finset.range (2 * n + 1), (2 * n).choose n := by
        apply Finset.sum_le_sum
        intro k hk
        simpa using Nat.choose_le_middle k (2 * n)
      _ = _ := by simp
  rw [h427 n]
  have hbq : (4 : ℚ) ^ n ≤ (2 * (n : ℚ) + 1) * ((2 * n).choose n : ℚ) := by exact_mod_cast hb
  push_cast
  apply (div_le_iff₀ (by positivity : (0 : ℚ) < (2 * n + 1) * (n + 1))).2
  calc
    (4 : ℚ) ^ n ≤ (2 * (n : ℚ) + 1) * ((2 * n).choose n : ℚ) := hbq
    _ = (2 * (n : ℚ) + 1) * (((2 * n).choose n : ℚ) / (n + 1) * (n + 1)) := by
      rw [div_mul_cancel₀ _ (by positivity : (n : ℚ) + 1 ≠ 0)]
    _ = _ := by ring
