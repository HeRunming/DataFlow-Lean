import Mathlib

open MeasureTheory ProbabilityTheory

namespace RademacherTailBound

 theorem rademacher_tail_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) (hN : 0 < N)
    (X : Fin N → Ω → ℝ)
    (a : Fin N → ℝ)
    (hX_measurable : ∀ i : Fin N, Measurable (X i))
    (hX_independent : iIndepFun X μ)
    (hX_rademacher :
      ∀ i : Fin N,
        ENNReal.toReal (μ {ω : Ω | X i ω = (1 : ℝ)}) = (1 / 2 : ℝ) ∧
        ENNReal.toReal (μ {ω : Ω | X i ω = (-1 : ℝ)}) = (1 / 2 : ℝ)) :
    ∀ t : ℝ, 0 ≤ t →
      ENNReal.toReal
          (μ {ω : Ω | t ≤ ∑ i : Fin N, a i * X i ω}) ≤
        if ((∑ i : Fin N, (a i)^2) : ℝ) = 0 then
          if t = 0 then (1 : ℝ) else 0
        else
          Real.exp
            (-t^2 / (2 * ((∑ i : Fin N, (a i)^2) : ℝ))) := by
  sorry

end RademacherTailBound
