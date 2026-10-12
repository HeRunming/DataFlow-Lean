import Mathlib

open MeasureTheory
open scoped BigOperators

noncomputable def headsCount {Ω : Type*}
    (head : ∀ N : ℕ, Fin N → Ω → Prop)
    (N : ℕ) (ω : Ω) : ℝ := by
  classical
  exact ((∑ i : Fin N, if head N i ω then (1 : ℝ) else (0 : ℝ)) : ℝ)

theorem chebyshev_heads_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (head : ∀ N : ℕ, Fin N → Ω → Prop)
    (h_head_measurable :
      ∀ (N : ℕ) (i : Fin N),
        MeasurableSet {ω : Ω | head N i ω})
    (h_head_joint :
      ∀ (N : ℕ) (A : Finset (Fin N)),
        μ {ω : Ω | ∀ i ∈ A, head N i ω} =
          ((1 : ENNReal) / (2 : ENNReal)) ^ A.card)
    (h_headsCount_measurable :
      ∀ (N : ℕ), Measurable (headsCount head N))
    (h_headsCount_memLp :
      ∀ (N : ℕ), MemLp (headsCount head N) (2 : ENNReal) μ)
    (N : ℕ) (hN : 0 < N) :
    μ {ω : Ω |
        (3 : ℝ) / (4 : ℝ) * (N : ℝ) ≤ headsCount head N ω} ≤
        μ {ω : Ω |
          (N : ℝ) / (4 : ℝ) ≤
            |headsCount head N ω - (N : ℝ) / (2 : ℝ)|} ∧
      μ {ω : Ω |
          (N : ℝ) / (4 : ℝ) ≤
            |headsCount head N ω - (N : ℝ) / (2 : ℝ)|} ≤
        ENNReal.ofReal ((4 : ℝ) / (N : ℝ)) := by
  sorry

theorem chebyshev_heads_probability_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (head : ∀ N : ℕ, Fin N → Ω → Prop)
    (h_rate :
      ∀ N : ℕ, 0 < N →
        μ {ω : Ω |
            (3 : ℝ) / (4 : ℝ) * (N : ℝ) ≤ headsCount head N ω} ≤
          ENNReal.ofReal ((4 : ℝ) / (N : ℝ))) :
    Filter.Tendsto
      (fun N : ℕ =>
        μ {ω : Ω |
            (3 : ℝ) / (4 : ℝ) * (N : ℝ) ≤ headsCount head N ω})
      Filter.atTop
      (nhds (0 : ENNReal)) := by
  sorry
