import Mathlib

noncomputable section
open Classical

namespace FiniteSetMedian

def IsMedian (s : Finset ℝ) (M : ℝ) : Prop :=
  (2 : ℕ) * (s.filter (fun x : ℝ => x ≤ M)).card ≥ s.card ∧
  (2 : ℕ) * (s.filter (fun x : ℝ => M ≤ x)).card ≥ s.card

theorem median_definition (s : Finset ℝ) (M : ℝ) :
    IsMedian s M ↔
      (2 : ℕ) * (s.filter (fun x : ℝ => x ≤ M)).card ≥ s.card ∧
      (2 : ℕ) * (s.filter (fun x : ℝ => M ≤ x)).card ≥ s.card := by sorry

end FiniteSetMedian
