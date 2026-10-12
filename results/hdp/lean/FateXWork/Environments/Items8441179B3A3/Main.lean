import Mathlib

def empiricalRisk {α : Type*} (n : ℕ) (X : Fin n → α) (T : α → Bool) (f : α → Bool) : ℚ :=
  ((Finset.univ.filter (fun i => f (X i) ≠ T (X i))).card : ℚ) / (n : ℚ)

theorem empirical_risk_minimization_classification
    {α : Type*} (n : ℕ) (X : Fin n → α) (T : α → Bool)
    (F : Set (α → Bool)) (hF : F.Nonempty) (hn : 0 < n) :
    ∃ f ∈ F, ∀ g ∈ F, empiricalRisk n X T f ≤ empiricalRisk n X T g := by
  classical
  let c := fun f : α → Bool => (Finset.univ.filter (fun i : Fin n => f (X i) ≠ T (X i))).card
  have hex : ∃ k : ℕ, ∃ f ∈ F, c f = k := by
    obtain ⟨f, hf⟩ := hF
    exact ⟨c f, f, hf, rfl⟩
  obtain ⟨f, hf, heq⟩ := Nat.find_spec hex
  refine ⟨f, hf, ?_⟩
  intro g hg
  have hle : c f ≤ c g := by
    rw [heq]
    exact Nat.find_min' hex ⟨g, hg, rfl⟩
  have hcast : (c f : ℚ) ≤ (c g : ℚ) := Nat.cast_le.mpr hle
  exact div_le_div_of_nonneg_right hcast (le_of_lt (Nat.cast_pos.mpr hn))
