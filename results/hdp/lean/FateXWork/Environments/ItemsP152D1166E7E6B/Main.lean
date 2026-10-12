import Mathlib

noncomputable section

open scoped Real

 def sphereNeighborhood (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n))) (t : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ‖x‖ = Real.sqrt (n : ℝ) ∧ ∃ y ∈ A, ‖x - y‖ ≤ t}

theorem mem_sphereNeighborhood_iff
    (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n))) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ sphereNeighborhood n A t ↔
      ‖x‖ = Real.sqrt (n : ℝ) ∧ ∃ y ∈ A, ‖x - y‖ ≤ t := by
  set_option maxHeartbeats 5000 in
    first | (rfl; done) | (assumption; done) | (simp; done) | (norm_num; done) | (omega; done) | (linarith; done) | (ring; done) | (simp_all [sphereNeighborhood]; done)
