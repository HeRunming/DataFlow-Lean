import Mathlib

def IsConvexBodySet {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  Bornology.IsBounded K ∧ Convex ℝ K ∧ Set.Nonempty (interior K)

theorem isConvexBodySet_iff (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))) :
    IsConvexBodySet K ↔
      Bornology.IsBounded K ∧ Convex ℝ K ∧ Set.Nonempty (interior K) := by
  rfl
