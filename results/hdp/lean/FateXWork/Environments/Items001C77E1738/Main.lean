import Mathlib

theorem caratheodory_convex_combination
    (n : ℕ) (T : Set (Fin n → ℝ)) :
    ∀ x : Fin n → ℝ,
      x ∈ convexHull ℝ T →
        ∃ k : ℕ,
          k ≤ n + 1 ∧
            ∃ points : Fin k → Fin n → ℝ,
              (∀ i : Fin k, points i ∈ T) ∧
                ∃ coeff : Fin k → ℝ,
                  (∀ i : Fin k, (0 : ℝ) ≤ coeff i) ∧
                    (∑ i : Fin k, coeff i : ℝ) = (1 : ℝ) ∧
                      x = (∑ i : Fin k, coeff i • points i : Fin n → ℝ) := by
  classical
  intro x hx
  obtain ⟨ι, _, z, w, hz, ha, hw, hsum, hcomb⟩ :=
    eq_pos_convex_span_of_mem_convexHull hx
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  refine ⟨Fintype.card ι, ?_, (z ∘ e.symm), ?_, (w ∘ e.symm), ?_, ?_, ?_⟩
  · have h := ha.card_le_finrank_succ
    have hdim := Submodule.finrank_le (vectorSpan ℝ (Set.range z))
    simp only [Module.finrank_pi, Fintype.card_fin] at hdim
    omega
  · intro i
    exact hz (Set.mem_range.mpr ⟨e.symm i, rfl⟩)
  · intro i
    exact (hw (e.symm i)).le
  · exact (e.symm.sum_comp w).trans hsum
  · exact hcomb.symm.trans (e.symm.sum_comp (fun j => w j • z j)).symm
