import Mathlib

def bracket (n : ℕ) : Finset ℕ := Finset.Icc 1 n

theorem bracket_spec (n : ℕ) : ∀ k : ℕ, k ∈ bracket n ↔ 1 ≤ k ∧ k ≤ n := by
  set_option maxHeartbeats 5000 in
    first | (rfl; done) | (assumption; done) | (simp; done) | (norm_num; done) | (omega; done) | (linarith; done) | (ring; done) | (simp_all [bracket]; done)
