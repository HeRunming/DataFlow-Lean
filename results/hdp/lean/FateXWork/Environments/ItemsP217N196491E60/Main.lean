import Mathlib

/-!
Formalization of the recalled definition of Minkowski sum and difference.

Source proof / Prover notes: This source entry is a definition/notation recall,
not a proposition requiring proof. Membership is expressed by witnesses from the
input sets and the corresponding pointwise operation.
-/

namespace FateXWork.Environments.ItemsP217N196491E60

/-- The Minkowski sum of two sets, corresponding to `T + S` in the source.

Source proof: unavailable; the source recalls a definition.
Proof sketch: membership means that the point is `t + s` for witnesses
`t ∈ T` and `s ∈ S`.
Prover notes: no proof obligation is generated for this definition.
-/
def minkowskiAdd {α : Type*} [Add α] (T S : Set α) : Set α :=
  {x | ∃ t ∈ T, ∃ s ∈ S, x = t + s}

/-- The Minkowski difference of two sets, corresponding to `T - S` in the source.

Source proof: unavailable; the source recalls a definition.
Proof sketch: membership means that the point is `t - s` for witnesses
`t ∈ T` and `s ∈ S`.
Prover notes: no proof obligation is generated for this definition.
-/
def minkowskiSub {α : Type*} [Sub α] (T S : Set α) : Set α :=
  {x | ∃ t ∈ T, ∃ s ∈ S, x = t - s}

scoped[ItemsP217N196491E60] infixl:65 " +ᵐ " => FateXWork.Environments.ItemsP217N196491E60.minkowskiAdd
scoped[ItemsP217N196491E60] infixl:65 " -ᵐ " => FateXWork.Environments.ItemsP217N196491E60.minkowskiSub

end FateXWork.Environments.ItemsP217N196491E60
