import Mathlib

open scoped BigOperators

/-- The value in `{-1, 1}` represented by a Boolean coordinate. -/
def signValue (b : Bool) : ℝ :=
  if b then (1 : ℝ) else (-1 : ℝ)

/-- The real vector represented by a Boolean vector. -/
def vectorValue (n : Nat) (x : Fin n → Bool) : Fin n → ℝ :=
  fun i : Fin n => signValue (x i)

/-- The feasible vectors for the integer quadratic optimization problem. -/
abbrev Feasible (n : Nat) := Fin n → Bool

/-- The quadratic objective associated with a real matrix and a feasible vector. -/
def quadraticObjective
    (n : Nat)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (x : Feasible n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, A i j * vectorValue n x i * vectorValue n x j

/-- The feasible set has cardinality `2 ^ n`, and a maximizer exists. -/
theorem semidefinite_program_integer_quadratic_optimization
    (n : Nat)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j : Fin n, A i j = A j i) :
    Fintype.card (Feasible n) = 2 ^ n ∧
      ∃ x : Feasible n,
        ∀ y : Feasible n,
          quadraticObjective n A y ≤ quadraticObjective n A x := by
  classical
  have _ := hA
  constructor
  · simp [Feasible]
  · let s : Finset ℝ := (Finset.univ : Finset (Feasible n)).image
        (fun x => quadraticObjective n A x)
    have hs : s.Nonempty := by
      simp [s]
    let m : ℝ := s.max' hs
    have hm : m ∈ s := by
      exact Finset.max'_mem s hs
    obtain ⟨x, hxmem, hx⟩ := Finset.mem_image.mp hm
    refine ⟨x, ?_⟩
    intro y
    have hy : quadraticObjective n A y ∈ s := by
      exact Finset.mem_image.mpr ⟨y, Finset.mem_univ y, rfl⟩
    rw [hx]
    exact Finset.le_max' s _ hy
