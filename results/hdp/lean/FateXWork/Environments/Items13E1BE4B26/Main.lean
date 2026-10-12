import Mathlib

/-!
# Exercise 1.3: finite Jensen inequality

The source's `ℝⁿ` is represented by `Fin n → ℝ`. Part (b) represents a
finite-valued random vector by a function on a finite sample type together
with its probability mass function.
-/

namespace FateXWork.Environments.Items13E1BE4B26

/-- Exercise 1.3(a): binary convexity on a convex set is equivalent to Jensen's
inequality for every finite family of points and nonnegative weights summing
to one.

Source proof: no proof is supplied. Prover notes: for the forward implication,
apply the finite Jensen theorem `ConvexOn.map_sum_le` (or induct on the finite
index set). For the reverse implication, specialize the finite-family property
to two points with weights `a` and `b`. -/
theorem convexOn_iff_finset_weighted_sum {n : ℕ} (K : Set (Fin n → ℝ))
    (hK : Convex ℝ K) (f : (Fin n → ℝ) → ℝ) :
    ConvexOn ℝ K f ↔
      ∀ (m : ℕ) (x : Fin m → Fin n → ℝ) (w : Fin m → ℝ),
        (∀ i, x i ∈ K) →
        (∀ i, 0 ≤ w i) →
        (∑ i, w i) = 1 →
        f (∑ i, w i • x i) ≤ ∑ i, w i * f (x i) := by
  sorry

/-- Exercise 1.3(b): Jensen's inequality for a random vector on a finite
probability space. The two displayed finite sums are respectively `𝔼 X` and
`𝔼 (f X)`.

Source proof: no proof is supplied. Prover notes: apply part (a) to the family
`X ω` with weights `p ω`; the assumptions say precisely that these weights are
nonnegative and sum to one. -/
theorem finite_jensen_inequality {n : ℕ} {Ω : Type*} [Fintype Ω]
    (p : Ω → ℝ) (X : Ω → Fin n → ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : ConvexOn ℝ Set.univ f)
    (hp_nonneg : ∀ ω, 0 ≤ p ω) (hp_sum : ∑ ω, p ω = 1) :
    f (∑ ω, p ω • X ω) ≤ ∑ ω, p ω * f (X ω) := by
  sorry

end FateXWork.Environments.Items13E1BE4B26
