import Mathlib

noncomputable def upperPairCount (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun e : Fin n × Fin n => e.1 < e.2)).card

noncomputable def upperEdgeCount (n : ℕ) (H : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact (Finset.univ.filter (fun e : Fin n × Fin n =>
    e.1 < e.2 ∧ H.Adj e.1 e.2)).card

noncomputable def vertexDegreeCount (n : ℕ) (H : SimpleGraph (Fin n))
    (i : Fin n) : ℕ := by
  classical
  exact (Finset.univ.filter (fun j : Fin n => H.Adj i j)).card

theorem erdos_renyi_all_degrees_concentrated :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (p : NNReal), p ≤ 1 →
        ∀ (Ω : Type*) [MeasurableSpace Ω]
          (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
          (G : Ω → SimpleGraph (Fin n)),
          (∀ H : SimpleGraph (Fin n), MeasurableSet {ω : Ω | G ω = H}) →
          (∀ H : SimpleGraph (Fin n),
            μ {ω : Ω | G ω = H} =
              ((p ^ upperEdgeCount n H *
                (1 - p) ^ (upperPairCount n - upperEdgeCount n H) : NNReal) : ENNReal)) →
          C * Real.log (n : ℝ) ≤ ((n - 1 : ℕ) : ℝ) * (p : ℝ) →
          (0.99 : ENNReal) ≤
            μ {ω : Ω |
              ∀ i : Fin n,
                (0.9 : ℝ) * (((n - 1 : ℕ) : ℝ) * (p : ℝ)) ≤
                  (vertexDegreeCount n (G ω) i : ℝ) ∧
                (vertexDegreeCount n (G ω) i : ℝ) ≤
                  (1.1 : ℝ) * (((n - 1 : ℕ) : ℝ) * (p : ℝ))} := by
  sorry
