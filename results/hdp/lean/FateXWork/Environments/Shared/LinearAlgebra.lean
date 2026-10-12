import Mathlib

/-!
# Shared linear algebra vocabulary

Authoritative definitions for the matrix objects that recur across the HDP
batches: matrix-vector action, the quadratic form of a square matrix, and the
rank-one outer product of a vector with itself.

## Namespace

Every declaration in this file lives in the namespace
`FateXWork.Shared.LinearAlgebra`, nested under the common root
`FateXWork.Shared` shared by all domain modules (`FateXWork.Shared.Basic`,
`.Analysis`, `.Probability`, `.Convexity`). The nesting is deliberate: 198 of the
batch sources declare their objects at the top level, so an un-namespaced shared
definition would collide with a batch definition of the same name as soon as a
batch imports this module. Namespacing keeps the shared vocabulary and the batch
vocabulary disjoint, so both compile side by side.

## Conventions

Matrices are `Matrix (Fin m) (Fin n) ℝ`, and vectors `Fin n → ℝ`. `matrixAction`,
`operatorNorm`, `euclideanOperatorNorm` and `frobeniusNorm` are the norm-theoretic
companions of these objects and live in `FateXWork.Shared.Analysis`; they are not
duplicated here. `matrixAction` agreed with Mathlib's `Matrix.mulVec` on the nose
and is recorded as such below rather than redefined.
-/

open scoped BigOperators

namespace FateXWork.Shared.LinearAlgebra

/-- The action `x ↦ A x` of a real matrix on a vector, `(A x) i = ∑ j, A i j * x j`.
This is Mathlib's `Matrix.mulVec`, named as the corpus names it. -/
def matrixAction {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) : Fin m → ℝ :=
  A.mulVec x

/-- The quadratic form `v ↦ vᵀ A v = ∑ i, ∑ j, v i * A i j * v j` of a square matrix. -/
def quadraticForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, v i * A i j * v j

/-- The rank-one outer product `u uᵀ`, the matrix with entries `(u i) * (u j)`. -/
def outerProduct {n : ℕ} (u : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => u i * u j

/-- The standard basis vector `e i` of `ℝⁿ`. -/
def basisVector {n : ℕ} (i : Fin n) : Fin n → ℝ :=
  fun j => if j = i then 1 else 0

/-- `A` is symmetric: `A i j = A j i`. Mathlib's `Matrix.IsSymm`, under the corpus
name. -/
def IsSymmetricMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  A.IsSymm

/-- The quadratic form is the inner product of `v` with the matrix action on `v`:
`quadraticForm A v = dot v (A v)`.

This is the usable form of the definition: it identifies `vᵀ A v` with the
Mathlib expression `Matrix.dotProduct v (A.mulVec v)` and makes available the
whole `Matrix.mulVec` API. -/
lemma quadraticForm_eq_dot_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) :
    quadraticForm A v = dotProduct v (A.mulVec v) := by
  simp only [quadraticForm, Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The matrix action is Mathlib's `Matrix.mulVec`, definitionally. -/
lemma matrixAction_eq_mulVec {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℝ) : matrixAction A x = A.mulVec x :=
  rfl

/-- The outer product `u uᵀ` is symmetric. -/
lemma outerProduct_isSymm {n : ℕ} (u : Fin n → ℝ) : (outerProduct u).IsSymm := by
  ext i j
  simp only [outerProduct]
  exact mul_comm _ _

/-- Applying the outer product `u uᵀ` to `x` returns `(∑ j, u j * x j) • u`. -/
lemma matrixAction_outerProduct {n : ℕ} (u x : Fin n → ℝ) :
    matrixAction (outerProduct u) x = (∑ j : Fin n, u j * x j) • u := by
  funext i
  simp only [matrixAction, Matrix.mulVec, dotProduct, outerProduct, Pi.smul_apply,
    smul_eq_mul]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

end FateXWork.Shared.LinearAlgebra
