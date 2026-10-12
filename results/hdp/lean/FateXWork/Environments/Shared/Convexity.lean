import Mathlib

/-!
# Shared convexity vocabulary

Authoritative definitions for the convex-geometric objects that recur across the
HDP batches: the convex hull of a finite family and the vertices of a convex set.

## Namespace

Every declaration in this file lives in the namespace
`FateXWork.Shared.Convexity`, nested under the common root `FateXWork.Shared`
shared by all domain modules (`FateXWork.Shared.Basic`, `.Analysis`,
`.Probability`, `.LinearAlgebra`). The nesting is deliberate: 198 of the batch
sources declare their objects at the top level, so an un-namespaced shared
definition would collide with a batch definition of the same name as soon as a
batch imports this module. Namespacing keeps the shared vocabulary and the batch
vocabulary disjoint, so both compile side by side.

## Conventions

Both definitions are stated over an arbitrary real module rather than over
`EuclideanSpace ℝ (Fin n)`, so that they apply to the polytopes of the corpus
without fixing a dimension. `finiteConvexHull` is `convexHull ℝ (Set.range v)`:
the standard `convexHull` of Mathlib, restricted to an indexed finite family, and
equal to the set of convex combinations of the family. `IsVertex` is membership
in `Set.extremePoints ℝ`, the standard extreme-point notion; on a polytope this
is exactly "vertex".
-/

open scoped BigOperators

namespace FateXWork.Shared.Convexity

/-- The convex hull of a finite family `v : Fin N → E`, as the convex hull of its
range: the set of convex combinations `∑ i, c i • v i` with `c i ≥ 0` and
`∑ i, c i = 1`. -/
def finiteConvexHull {E : Type*} [AddCommMonoid E] [Module ℝ E] {N : ℕ}
    (v : Fin N → E) : Set E :=
  convexHull ℝ (Set.range v)

/-- `x` is a vertex of `P`: an extreme point of `P`, i.e. `x ∈ P` and `x` lies in
no open segment with both endpoints in `P`. -/
def IsVertex {E : Type*} [AddCommMonoid E] [Module ℝ E] (P : Set E) (x : E) : Prop :=
  x ∈ Set.extremePoints ℝ P

/-- A vertex lies in the set. -/
lemma IsVertex.mem {E : Type*} [AddCommMonoid E] [Module ℝ E] {P : Set E} {x : E}
    (h : IsVertex P x) : x ∈ P := by
  rw [IsVertex] at h
  exact (mem_extremePoints.mp h).1

/-- Every point of a finite family belongs to its convex hull. -/
lemma self_mem_finiteConvexHull {E : Type*} [AddCommMonoid E] [Module ℝ E] {N : ℕ}
    (v : Fin N → E) (i : Fin N) : v i ∈ finiteConvexHull v := by
  rw [finiteConvexHull]
  exact subset_convexHull ℝ (Set.range v) (Set.mem_range_self i)

end FateXWork.Shared.Convexity
