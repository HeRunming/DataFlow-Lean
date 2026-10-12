import Mathlib

/-!
# Shared analysis vocabulary

Authoritative definitions for the analytic objects that recur across the HDP
batches: Euclidean norms and inner products, matrix action, the norms induced on
matrices, and the Euclidean unit sphere and ball.

## Namespace

Every declaration in this file lives in the namespace
`FateXWork.Shared.Analysis`, nested under the common root `FateXWork.Shared`
shared by all domain modules (`FateXWork.Shared.Basic`, `.Probability`,
`.Convexity`, `.LinearAlgebra`). The nesting is deliberate: 198 of the batch
sources declare their objects at the top level, so an un-namespaced shared
definition would collide with a batch definition of the same name as soon as a
batch imports this module. Namespacing keeps the shared vocabulary and the batch
vocabulary disjoint, so both compile side by side.

## Type conventions

Definitions here use Mathlib's standard types directly, never a batch-local
alias: vectors are `Fin n → ℝ` (or an arbitrary `ι → ℝ` with `[Fintype ι]`),
and `unitSphere`/`unitBall` are stated on `EuclideanSpace ℝ (Fin n)`.

That split is not cosmetic. `Fin n → ℝ` inherits the *sup* norm from the
product, not the Euclidean one, and `EuclideanSpace ℝ (Fin n)` is
`WithLp 2 (Fin n → ℝ)`, which is not definitionally equal to `Fin n → ℝ`. So a
`Set (Fin n → ℝ)` written as `{x | ‖x‖ = 1}` would be the sup-norm sphere, not
the Euclidean sphere: any spherical statement must either go through
`EuclideanSpace ℝ (Fin n)` with `‖·‖`, or through the explicit `l2Norm` defined
below.
-/

open scoped BigOperators

namespace FateXWork.Shared.Analysis

/-- The Euclidean (`ℓ²`) norm `√(∑ i, x i ^ 2)` of a finite real family. -/
noncomputable def l2Norm {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i, (x i) ^ 2)

/-- The Euclidean norm on `ℝⁿ`, the case of `l2Norm` at `ι = Fin n`. -/
noncomputable def euclideanNorm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  l2Norm x

/-- The Euclidean inner product `∑ i, x i * y i`. -/
def dot {ι : Type*} [Fintype ι] (x y : ι → ℝ) : ℝ :=
  ∑ i, x i * y i

/-- The operator norm of a matrix induced by the Euclidean norm on both sides:
the least `K ≥ 0` with `‖A x‖₂ ≤ K * ‖x‖₂` for every `x`.

The matrix action `A x` used here is `FateXWork.Shared.LinearAlgebra.matrixAction`,
which is Mathlib's `Matrix.mulVec`; this module spells it out inline so that
`Analysis` does not depend on `LinearAlgebra` in the import order. -/
noncomputable def operatorNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  sInf {K : ℝ | 0 ≤ K ∧ ∀ x : Fin n → ℝ, l2Norm (A.mulVec x) ≤ K * l2Norm x}

/-- The Euclidean-induced operator norm, under the name that says which norm
induces it; definitionally `operatorNorm`. -/
noncomputable abbrev euclideanOperatorNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  operatorNorm A

/-- The Frobenius norm `√(∑ i, ∑ j, A i j ^ 2)`, the Euclidean norm of the entries. -/
noncomputable def frobeniusNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin m, ∑ j : Fin n, (A i j) ^ 2)

/-- The Euclidean unit sphere of `ℝⁿ`, as a subset of `EuclideanSpace ℝ (Fin n)`. -/
def unitSphere (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  Metric.sphere 0 1

/-- The closed Euclidean unit ball of `ℝⁿ`, as a subset of `EuclideanSpace ℝ (Fin n)`. -/
def unitBall (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  Metric.closedBall 0 1

/-- The Euclidean norm is nonnegative. -/
lemma l2Norm_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) : 0 ≤ l2Norm x :=
  Real.sqrt_nonneg _

/-- The Euclidean norm is nonnegative. -/
lemma euclideanNorm_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ euclideanNorm x :=
  Real.sqrt_nonneg _

/-- Squaring the Euclidean norm recovers the sum of squares. -/
lemma sq_l2Norm {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    (l2Norm x) ^ 2 = ∑ i, (x i) ^ 2 := by
  rw [l2Norm, Real.sq_sqrt]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- The Euclidean inner product is symmetric. -/
lemma dot_comm {ι : Type*} [Fintype ι] (x y : ι → ℝ) : dot x y = dot y x := by
  simp only [dot]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The Frobenius norm is nonnegative. -/
lemma frobeniusNorm_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    0 ≤ frobeniusNorm A :=
  Real.sqrt_nonneg _

end FateXWork.Shared.Analysis
