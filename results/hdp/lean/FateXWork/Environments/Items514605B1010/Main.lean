import Mathlib

/-!
Formalization of source item 5.1.4. The source's "area" is represented here
by Lebesgue volume; the perimeter formulation is recorded as a scope change in
`Blueprint.md`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace FateXWork.Environments.Items514605B1010

/-- The closed Euclidean ball used in the source statement. -/
def euclideanBall (n : ℕ) (center : EuclideanSpace ℝ (Fin n)) (radius : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  Metric.closedBall center radius

/-- The metric ε-neighborhood of a set, matching the source's `A_ε`. -/
def epsilonNeighborhood {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n))) (ε : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∃ y ∈ A, dist x y ≤ ε}

/--
Source proof: no proof is supplied in the QA source excerpt; this is the
isoperimetric theorem asserting that a Euclidean ball of prescribed volume is
optimal, together with the ε-neighborhood assertion.

Proof sketch: use the Euclidean isoperimetric inequality and the corresponding
Brunn–Minkowski consequence for parallel sets. Prover notes: the current draft
uses Lebesgue volume for both source occurrences of “area”; see `Blueprint.md`
for this intentional representation change.
-/
theorem isoperimetric_inequality_on_euclidean_space
    {n : ℕ} (hn : 0 < n) (A : Set (EuclideanSpace ℝ (Fin n)))
    (hA : MeasurableSet A) (hfinite : volume A ≠ (⊤ : ℝ≥0∞)) :
    ∃ (center : EuclideanSpace ℝ (Fin n)) (radius : ℝ),
      0 ≤ radius ∧
      volume (euclideanBall n center radius) = volume A ∧
      (∀ C : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet C →
        volume C = volume A →
        volume (euclideanBall n center radius) ≤ volume C) ∧
      (∀ ε : ℝ, 0 < ε →
        volume (epsilonNeighborhood (euclideanBall n center radius) ε) ≤
          volume (epsilonNeighborhood A ε)) := by
  sorry

end FateXWork.Environments.Items514605B1010
