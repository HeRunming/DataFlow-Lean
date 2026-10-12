import Mathlib

/-! Formalization of HDP, Section 8.3, item 8.3.12.

The source identifies strips in Euclidean space and records the VC-dimension
bound supplied by Example 8.3.5. The definitions below make the strip class
and the finite-set notion of shattering explicit.
-/

namespace FateXWork.Environments.Items831209CDFAB3

noncomputable section

def strip (n : ℕ) (a : Fin n → ℝ) (b c : ℝ) : Set (Fin n → ℝ) :=
  {x | |∑ i, a i * x i - b| ≤ c}

def stripClass (n : ℕ) : Set (Set (Fin n → ℝ)) :=
  {S | ∃ (a : Fin n → ℝ) (b c : ℝ), S = strip n a b c}

def shatters {α : Type*} (F : Set (Set α)) (s : Finset α) : Prop :=
  ∀ t : Finset α, t ⊆ s → ∃ A ∈ F, ∀ x ∈ s, x ∈ A ↔ x ∈ t

def vcDimension {α : Type*} (F : Set (Set α)) : ℕ := by
  classical
  if h : ∃ d : ℕ, ∀ s : Finset α, shatters F s → s.card ≤ d then
    exact Nat.find h
  else exact 0

/--
Source proof: no independent proof text is supplied; the source invokes
Example 8.3.5 for the estimate. Prover notes: use the strip and shattering
interfaces above to formalize the cited VC bound, then derive the displayed
linear estimate arithmetically from `1 ≤ n`.
-/
theorem strips_vcDimension_le (n : ℕ) (hn : 1 ≤ n) :
    vcDimension (stripClass n) ≤ 20 * (n + 1) ∧
      20 * (n + 1) ≤ 40 * n := by
  sorry

end
end FateXWork.Environments.Items831209CDFAB3
