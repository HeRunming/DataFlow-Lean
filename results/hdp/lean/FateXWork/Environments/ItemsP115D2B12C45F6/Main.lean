import Mathlib

/-- Two subsets of the real numbers are `δ`-separated when every point of the
first set is at least `δ` away from every point of the second set. -/
def DeltaSeparated (I J : Set ℝ) (δ : ℝ) : Prop :=
  ∀ x ∈ I, ∀ y ∈ J, δ ≤ |x - y|

 theorem deltaSeparated_iff (I J : Set ℝ) (δ : ℝ) :
    DeltaSeparated I J δ ↔ ∀ x ∈ I, ∀ y ∈ J, δ ≤ |x - y| := by
  set_option maxHeartbeats 5000 in
    first | (rfl; done) | (assumption; done) | (simp; done) | (norm_num; done) | (omega; done) | (linarith; done) | (ring; done) | (simp_all [DeltaSeparated]; done)
