import Mathlib

open MeasureTheory

 theorem holder_inequality_Lp
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (p p' : ENNReal)
    (hp : (1 : ENNReal) ≤ p)
    (hp' : (1 : ENNReal) ≤ p')
    (hconj : p⁻¹ + (p')⁻¹ = (1 : ENNReal))
    (X Y : Ω → ℝ)
    (hX_measurable : Measurable X)
    (hY_measurable : Measurable Y)
    (hX_mem : MemLp X p μ)
    (hY_mem : MemLp Y p' μ) :
    eLpNorm (fun ω : Ω => X ω * Y ω) (1 : ENNReal) μ ≤
      eLpNorm X p μ * eLpNorm Y p' μ := by
  haveI : ENNReal.HolderConjugate p p' := ENNReal.holderConjugate_iff.mpr hconj
  have _ := hp
  have _ := hp'
  have _ := hX_measurable
  have _ := hY_measurable
  simpa only [Pi.smul_apply, smul_eq_mul] using
    (eLpNorm_smul_le_mul_eLpNorm (p := p) (q := p') (r := 1)
      hY_mem.1 hX_mem.1)
