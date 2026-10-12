import Mathlib

/-- A matrix is diagonal-free when every diagonal entry is zero. -/
def DiagonalFree {ι R : Type*} [Zero R] (A : Matrix ι ι R) : Prop :=
  ∀ i : ι, A i i = 0

theorem diagonalFree_iff {ι R : Type*} [Zero R] (A : Matrix ι ι R) :
    DiagonalFree A ↔ ∀ i : ι, A i i = 0 := by
  exact Iff.rfl
