import Mathlib

open MeasureTheory

noncomputable section

theorem chebyshev_inequality
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ)
    (hX_measurable : Measurable X)
    (mu sigma : ℝ)
    (hX_integrable : Integrable X P)
    (hX_centered_sq_integrable : Integrable (fun ω => (X ω - mu) ^ 2) P)
    (hmean : ∫ ω, X ω ∂P = mu)
    (hvariance : ∫ ω, (X ω - mu) ^ 2 ∂P = sigma ^ 2) :
    ∀ (t : ℝ), 0 < t →
      ENNReal.toReal (P {ω | t ≤ |X ω - mu|}) ≤ sigma ^ 2 / t ^ 2 := by
  intro t ht
  let Y : Ω → ℝ := fun ω => (X ω - mu) ^ 2
  have hY_nonneg : 0 ≤ᵐ[P] Y := Filter.Eventually.of_forall fun ω => sq_nonneg (X ω - mu)
  have hset : {ω | t ≤ |X ω - mu|} ⊆ {ω | t ^ 2 ≤ Y ω} := by
    intro ω hω
    change t ≤ |X ω - mu| at hω
    change t ^ 2 ≤ (X ω - mu) ^ 2
    have habs : 0 ≤ |X ω - mu| := abs_nonneg _
    have hs : |X ω - mu| ^ 2 = (X ω - mu) ^ 2 := sq_abs _
    nlinarith [sq_nonneg (|X ω - mu| - t)]
  have hmark := MeasureTheory.mul_meas_ge_le_integral_of_nonneg hY_nonneg hX_centered_sq_integrable (t ^ 2)
  have hprob : P {ω | t ≤ |X ω - mu|} ≤ P {ω | t ^ 2 ≤ Y ω} := measure_mono hset
  have hbound : t ^ 2 * (P {ω | t ^ 2 ≤ Y ω}).toReal ≤ ∫ ω, Y ω ∂P := by
    simpa [Measure.real_def] using hmark
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
  have hreal : (P {ω | t ≤ |X ω - mu|}).toReal ≤ (P {ω | t ^ 2 ≤ Y ω}).toReal := ENNReal.toReal_mono (measure_ne_top P _) hprob
  have hInt : (∫ ω, Y ω ∂P) = sigma ^ 2 := by simpa [Y] using hvariance
  calc
    (P {ω | t ≤ |X ω - mu|}).toReal ≤ (P {ω | t ^ 2 ≤ Y ω}).toReal := hreal
    _ ≤ sigma ^ 2 / t ^ 2 := (le_div_iff₀ ht2).2 (by nlinarith [hbound, hInt])
