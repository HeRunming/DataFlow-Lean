import Mathlib

open MeasureTheory

set_option linter.unusedVariables false in
 theorem two_sided_tail_union_bound
    {Ω : Type u}
    [MeasurableSpace Ω]
    (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (N : ℕ)
    (a : Fin N → ℝ)
    (X : Fin N → Ω → ℝ)
    (t : ℝ)
    (hX : ∀ i : Fin N, Measurable (X i)) :
    μ {ω : Ω | |(∑ i : Fin N, (a i * X i ω : ℝ))| ≥ t} ≤
      μ {ω : Ω | (∑ i : Fin N, (a i * X i ω : ℝ)) ≥ t} +
        μ {ω : Ω | -(∑ i : Fin N, (a i * X i ω : ℝ)) ≥ t} := by
  let S : Ω → ℝ := fun ω => ∑ i : Fin N, (a i * X i ω : ℝ)
  have hsub : {ω : Ω | |S ω| ≥ t} ⊆
      {ω : Ω | S ω ≥ t} ∪ {ω : Ω | -S ω ≥ t} := by
    intro ω hω
    change |S ω| ≥ t at hω
    rcases le_total 0 (S ω) with h | h
    · left
      simpa [abs_of_nonneg h] using hω
    · right
      have h' : S ω ≤ 0 := h
      simpa [abs_of_nonpos h'] using hω
  have hmeas : {ω : Ω | |S ω| ≥ t} =
      {ω : Ω | |(∑ i : Fin N, (a i * X i ω : ℝ))| ≥ t} := by
    rfl
  rw [← hmeas]
  apply (measure_mono hsub).trans
  simpa [S] using (measure_union_le ({ω : Ω | S ω ≥ t}) ({ω : Ω | -S ω ≥ t}))
