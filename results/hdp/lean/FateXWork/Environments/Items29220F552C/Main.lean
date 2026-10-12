import Mathlib

open MeasureTheory

namespace HoeffdingSignatures

noncomputable def expectation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) : ℝ :=
  MeasureTheory.integral μ X

noncomputable def twoPointMGF (p coeff : ℝ) : ℝ :=
  ((1 : ℝ) - p) * Real.exp (coeff * (-p)) +
    p * Real.exp (coeff * ((1 : ℝ) - p))

noncomputable def twoPointCGF (p coeff : ℝ) : ℝ :=
  Real.log (twoPointMGF p coeff)

noncomputable def cgfSlope (p coeff : ℝ) : ℝ :=
  p * Real.exp coeff / ((1 : ℝ) - p + p * Real.exp coeff) - p

noncomputable def cgfCurvature (p coeff : ℝ) : ℝ :=
  p * ((1 : ℝ) - p) * Real.exp coeff /
    (((1 : ℝ) - p + p * Real.exp coeff) ^ (2 : ℕ))

/-- The ordinary real derivative, expressed by its punctured difference-quotient limit. -/
def IsRealDerivative (f : ℝ → ℝ) (x d : ℝ) : Prop :=
  ∀ ε : ℝ, (0 : ℝ) < ε →
    ∃ δ : ℝ, (0 : ℝ) < δ ∧
      ∀ h : ℝ, (0 : ℝ) < |h| → |h| < δ →
        |(f (x + h) - f x) / h - d| < ε

/-- All ordinary expectations used in the bounded-variable statement are finite. -/
theorem bounded_integrability
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (a b : ℝ)
    (hX : Measurable X)
    (hX_mem : ∀ ω : Ω, a ≤ X ω ∧ X ω ≤ b) :
    Integrable X μ ∧
      ∀ coeff : ℝ,
        Integrable (fun ω : Ω => Real.exp (coeff * X ω)) μ ∧
        Integrable
          (fun ω : Ω => Real.exp (coeff * (X ω - expectation μ X))) μ ∧
        (0 : ℝ) < expectation μ (fun ω : Ω => Real.exp (coeff * X ω)) := by
  have hXint : Integrable X μ := by
    apply Integrable.mono' (integrable_const (μ := μ) (c := max |a| |b|)) hX.aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs]
    apply abs_le.2
    constructor <;> linarith [hX_mem ω |>.1, hX_mem ω |>.2,
      neg_abs_le a, le_abs_self b, le_max_left |a| |b|, le_max_right |a| |b|]
  refine ⟨hXint, fun coeff => ?_⟩
  have h1 := ProbabilityTheory.integrable_exp_mul_of_mem_Icc (μ := μ) (X := X)
    (a := a) (b := b) (t := coeff) hX.aemeasurable
    (Filter.Eventually.of_forall fun ω => hX_mem ω)
  have h2 := ProbabilityTheory.integrable_exp_mul_of_mem_Icc (μ := μ)
    (X := fun ω => X ω - expectation μ X) (a := a - expectation μ X)
    (b := b - expectation μ X) (t := coeff)
    (hX.aemeasurable.sub measurable_const.aemeasurable)
    (Filter.Eventually.of_forall fun ω =>
      ⟨sub_le_sub_right (hX_mem ω).1 _, sub_le_sub_right (hX_mem ω).2 _⟩)
  refine ⟨h1, h2, ?_⟩
  rw [expectation]
  have hn : 0 ≤ᵐ[μ] (fun ω : Ω => Real.exp (coeff * X ω)) :=
    Filter.Eventually.of_forall fun ω => Real.exp_nonneg _
  rw [integral_pos_iff_support_of_nonneg_ae hn h1]
  change 0 < μ {ω : Ω | Real.exp (coeff * X ω) ≠ 0}
  have hs : {ω : Ω | Real.exp (coeff * X ω) ≠ 0} = Set.univ := by
    ext ω
    simp [Real.exp_ne_zero]
  rw [hs]
  simp

private theorem exp_chord (p y c : ℝ) (hl : -p ≤ y) (hu : y ≤ 1-p) : Real.exp (c*y) ≤ (1-p-y)*Real.exp (c*(-p)) + (y+p)*Real.exp (c*(1-p)) := by
  have h := convexOn_exp.2 (Set.mem_univ (c*(-p))) (Set.mem_univ (c*(1-p))) (show 0 ≤ 1-p-y by linarith) (show 0 ≤ y+p by linarith) (show (1-p-y)+(y+p)=1 by ring)
  simp only [smul_eq_mul] at h
  convert h using 1 <;> congr 1 <;> ring

/-- Part (a): centering, unit-width normalization, and domination by a two-point law. -/
theorem normalized_two_point_reduction
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (a b : ℝ)
    (hX : Measurable X)
    (hX_mem : ∀ ω : Ω, a ≤ X ω ∧ X ω ≤ b)
    (hab : a < b) :
    let mean : ℝ := expectation μ X
    let p : ℝ := (mean - a) / (b - a)
    let Y : Ω → ℝ := fun ω : Ω => (X ω - mean) / (b - a)
    (0 : ℝ) ≤ p ∧ p ≤ (1 : ℝ) ∧
      Measurable Y ∧ Integrable Y μ ∧
      expectation μ Y = (0 : ℝ) ∧
      (((1 : ℝ) - p) - (-p) = (1 : ℝ)) ∧
      (∀ ω : Ω, -p ≤ Y ω ∧ Y ω ≤ (1 : ℝ) - p) ∧
      (∀ coeff : ℝ,
        Integrable (fun ω : Ω => Real.exp (coeff * Y ω)) μ ∧
        expectation μ (fun ω : Ω => Real.exp (coeff * Y ω)) ≤
          twoPointMGF p coeff) ∧
      (∀ coeff : ℝ,
        expectation μ (fun ω : Ω => Real.exp (coeff * (X ω - mean))) =
          expectation μ (fun ω : Ω => Real.exp ((coeff * (b - a)) * Y ω))) := by
  dsimp
  have hbounds := bounded_integrability μ X a b hX hX_mem
  have hXi : Integrable X μ := hbounds.1
  have hexp (coeff : ℝ) : Integrable (fun ω : Ω => Real.exp (coeff * X ω)) μ :=
    (hbounds.2 coeff).1
  have hcenterexp (coeff : ℝ) :
      Integrable (fun ω : Ω => Real.exp (coeff * (X ω - expectation μ X))) μ :=
    (hbounds.2 coeff).2.1
  have hchord (coeff y : ℝ) (hl : -((expectation μ X - a) / (b - a)) ≤ y)
      (hu : y ≤ 1 - ((expectation μ X - a) / (b - a))) :=
    exp_chord ((expectation μ X - a) / (b - a)) y coeff hl hu
  have hchord_at (coeff : ℝ) (ω : Ω)
      (hl : -((expectation μ X - a) / (b - a)) ≤
        (X ω - expectation μ X) / (b - a))
      (hu : (X ω - expectation μ X) / (b - a) ≤
        1 - ((expectation μ X - a) / (b - a))) :
      Real.exp (coeff * ((X ω - expectation μ X) / (b - a))) ≤
        (1 - ((expectation μ X - a) / (b - a)) -
            ((X ω - expectation μ X) / (b - a))) *
            Real.exp (coeff * (-((expectation μ X - a) / (b - a)))) +
          (((X ω - expectation μ X) / (b - a)) +
            ((expectation μ X - a) / (b - a))) *
            Real.exp (coeff * (1 - ((expectation μ X - a) / (b - a)))) :=
    hchord coeff ((X ω - expectation μ X) / (b - a)) hl hu
  have hmean_lower : a ≤ expectation μ X := by
    rw [expectation]
    simpa using (integral_mono_ae (integrable_const (μ := μ) (c := a)) hXi
      (Filter.Eventually.of_forall fun ω => hX_mem ω |>.1))
  have hmean_upper : expectation μ X ≤ b := by
    rw [expectation]
    simpa using (integral_mono_ae hXi (integrable_const (μ := μ) (c := b))
      (Filter.Eventually.of_forall fun ω => hX_mem ω |>.2))
  have hden : 0 < b - a := sub_pos.mpr hab
  have hp0 : 0 ≤ (expectation μ X - a) / (b - a) :=
    div_nonneg (sub_nonneg.mpr hmean_lower) (le_of_lt hden)
  have hp1 : (expectation μ X - a) / (b - a) ≤ 1 := by
    apply (div_le_iff₀ hden).2
    linarith
  have hYmeas : Measurable (fun ω : Ω => (X ω - expectation μ X) / (b - a)) :=
    (hX.sub measurable_const).div_const _
  have hYint : Integrable (fun ω : Ω => (X ω - expectation μ X) / (b - a)) μ := by
    exact (hXi.sub (integrable_const (μ := μ) (c := expectation μ X))).div_const _
  have hYzero : expectation μ (fun ω : Ω =>
      (X ω - expectation μ X) / (b - a)) = 0 := by
    rw [expectation, integral_div]
    rw [integral_sub hXi (integrable_const (μ := μ) (c := expectation μ X))]
    simp [expectation]
  have hYbounds : ∀ ω : Ω,
      -((expectation μ X - a) / (b - a)) ≤
        (X ω - expectation μ X) / (b - a) ∧
      (X ω - expectation μ X) / (b - a) ≤
        1 - (expectation μ X - a) / (b - a) := by
    intro ω
    constructor
    · have hrewrite : -((expectation μ X - a) / (b - a)) =
          (a - expectation μ X) / (b - a) := by
        field_simp
        ring
      rw [hrewrite]
      apply (div_le_div_iff_of_pos_right hden).2
      linarith [hX_mem ω |>.1]
    · have hrewrite : 1 - (expectation μ X - a) / (b - a) =
          (b - expectation μ X) / (b - a) := by
        field_simp
        ring
      rw [hrewrite]
      apply (div_le_div_iff_of_pos_right hden).2
      linarith [hX_mem ω |>.2]
  have hYexp (coeff : ℝ) : Integrable (fun ω : Ω => Real.exp (coeff *
      ((X ω - expectation μ X) / (b - a)))) μ := by
    convert hcenterexp (coeff / (b - a)) using 1 <;>
      field_simp [ne_of_gt hden]
  refine ⟨hp0, hp1, hYmeas, hYint, hYzero, by ring, hYbounds, ?_, ?_⟩
  · intro coeff
    let p : ℝ := (expectation μ X - a) / (b - a)
    let A : ℝ := Real.exp (coeff * (-p))
    let B : ℝ := Real.exp (coeff * (1 - p))
    have h1 : Integrable (fun ω : Ω => (1 - p -
        ((X ω - expectation μ X) / (b - a))) * A) μ := by
      simpa only [sub_mul] using
        ((integrable_const (μ := μ) (c := (1 - p) * A)).sub
          (hYint.mul_const A))
    have h2 : Integrable (fun ω : Ω =>
        (((X ω - expectation μ X) / (b - a)) + p) * B) μ := by
      simpa only [add_mul] using
        ((hYint.mul_const B).add
          (integrable_const (μ := μ) (c := p * B)))
    have hdom := h1.add h2
    have hm := integral_mono_ae (hYexp coeff) hdom
      (Filter.Eventually.of_forall fun ω =>
        exp_chord p ((X ω - expectation μ X) / (b - a)) coeff
          (by simpa [p] using (hYbounds ω).1)
          (by simpa [p] using (hYbounds ω).2))
    constructor
    · exact hYexp coeff
    · change (∫ ω, Real.exp (coeff *
          ((X ω - expectation μ X) / (b - a))) ∂μ) ≤
        twoPointMGF ((expectation μ X - a) / (b - a)) coeff
      have hz : (∫ ω, ((X ω - expectation μ X) / (b - a)) ∂μ) = 0 := by
        simpa [expectation] using hYzero
      have hi1 : (∫ ω, (1 - p -
          ((X ω - expectation μ X) / (b - a))) * A ∂μ) = (1 - p) * A := by
        calc
          _ = ∫ ω, ((1 - p) * A -
              ((X ω - expectation μ X) / (b - a)) * A) ∂μ := by
            apply integral_congr_ae
            filter_upwards [] with ω
            ring
          _ = (∫ ω, (1 - p) * A ∂μ) -
              (∫ ω, ((X ω - expectation μ X) / (b - a)) * A ∂μ) := by
            rw [integral_sub (integrable_const (μ := μ) (c := (1 - p) * A))
              (hYint.mul_const A)]
          _ = (1 - p) * A := by
            simp [integral_const, integral_mul_const, hz]
      have hi2 : (∫ ω, (((X ω - expectation μ X) / (b - a)) + p) * B ∂μ) = p * B := by
        calc
          _ = ∫ ω, (((X ω - expectation μ X) / (b - a)) * B + p * B) ∂μ := by
            apply integral_congr_ae
            filter_upwards [] with ω
            ring
          _ = (∫ ω, ((X ω - expectation μ X) / (b - a)) * B ∂μ) +
              (∫ ω, p * B ∂μ) := by
            rw [integral_add (hYint.mul_const B)
              (integrable_const (μ := μ) (c := p * B))]
          _ = p * B := by
            simp [integral_const, integral_mul_const, hz]
      calc
        _ ≤ ∫ ω, (1 - p - ((X ω - expectation μ X) / (b - a))) * A +
              (((X ω - expectation μ X) / (b - a)) + p) * B ∂μ := hm
        _ = (1 - p) * A + p * B := by rw [integral_add h1 h2, hi1, hi2]
        _ = twoPointMGF ((expectation μ X - a) / (b - a)) coeff := by
          simp [p, A, B, twoPointMGF]
  · intro coeff
    change (∫ ω, Real.exp (coeff * (X ω - expectation μ X)) ∂μ) =
      ∫ ω, Real.exp ((coeff * (b - a)) *
        ((X ω - expectation μ X) / (b - a))) ∂μ
    apply integral_congr_ae
    filter_upwards [] with ω
    congr 1
    field_simp [ne_of_gt hden] <;> ring

/-- The zero-width case is retained rather than divided by zero. -/
theorem degenerate_interval
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (a : ℝ)
    (hX : Measurable X)
    (hX_mem : ∀ ω : Ω, a ≤ X ω ∧ X ω ≤ a) :
    expectation μ X = a ∧
      ∀ coeff : ℝ,
        expectation μ
          (fun ω : Ω => Real.exp (coeff * (X ω - expectation μ X))) =
          (1 : ℝ) := by
  have hXa : X = fun _ => a := funext fun ω =>
    le_antisymm (hX_mem ω).2 (hX_mem ω).1
  subst X
  constructor
  · simp [expectation]
  · intro coeff
    simp [expectation]

/-- Part (b): the MGF and CGF of any centered, unit-width two-point random variable. -/
theorem two_point_cgf_computation
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (p : ℝ)
    (hp0 : (0 : ℝ) ≤ p) (hp1 : p ≤ (1 : ℝ))
    (hX : Measurable X)
    (hX_two_point : ∀ ω : Ω, X ω = -p ∨ X ω = (1 : ℝ) - p)
    (hmean : expectation μ X = (0 : ℝ)) :
    Integrable X μ ∧
      ∀ coeff : ℝ,
        Integrable (fun ω : Ω => Real.exp (coeff * X ω)) μ ∧
        (0 : ℝ) < expectation μ (fun ω : Ω => Real.exp (coeff * X ω)) ∧
        expectation μ (fun ω : Ω => Real.exp (coeff * X ω)) =
          twoPointMGF p coeff ∧
        Real.log (expectation μ (fun ω : Ω => Real.exp (coeff * X ω))) =
          twoPointCGF p coeff := by
  have hX_mem : ∀ ω : Ω, (-p : ℝ) ≤ X ω ∧ X ω ≤ 1 - p := by
    intro ω
    rcases hX_two_point ω with h | h
    · rw [h]
      constructor <;> linarith
    · rw [h]
      constructor <;> linarith
  have hbounds := bounded_integrability μ X (-p) (1 - p) hX hX_mem
  have hXi : Integrable X μ := hbounds.1
  have hexp (coeff : ℝ) :
      Integrable (fun ω : Ω => Real.exp (coeff * X ω)) μ :=
    (hbounds.2 coeff).1
  refine ⟨hXi, ?_⟩
  intro coeff
  have hpos : (0 : ℝ) < expectation μ (fun ω : Ω => Real.exp (coeff * X ω)) :=
    (hbounds.2 coeff).2.2
  have hmgf : expectation μ (fun ω : Ω => Real.exp (coeff * X ω)) =
      twoPointMGF p coeff := by
    let A : ℝ := Real.exp (coeff * (-p))
    let B : ℝ := Real.exp (coeff * (1 - p))
    have h1 : Integrable (fun ω : Ω => (1 - p - X ω) * A) μ := by
      simpa only [sub_mul] using
        ((integrable_const (μ := μ) (c := (1 - p) * A)).sub
          (hXi.mul_const A))
    have h2 : Integrable (fun ω : Ω => (X ω + p) * B) μ := by
      simpa only [add_mul] using
        ((hXi.mul_const B).add
          (integrable_const (μ := μ) (c := p * B)))
    have hpoint : ∀ ω : Ω,
        Real.exp (coeff * X ω) =
          (1 - p - X ω) * A + (X ω + p) * B := by
      intro ω
      rcases hX_two_point ω with h | h
      · rw [h]
        dsimp [A, B]
        ring
      · rw [h]
        dsimp [A, B]
        ring
    have hmean_int : (∫ ω, X ω ∂μ) = 0 := by
      simpa [expectation] using hmean
    have hi1 : (∫ ω, (1 - p - X ω) * A ∂μ) = (1 - p) * A := by
      calc
        _ = ∫ ω, ((1 - p) * A - X ω * A) ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with ω
          ring
        _ = (∫ ω, (1 - p) * A ∂μ) - (∫ ω, X ω * A ∂μ) := by
          rw [integral_sub (integrable_const (μ := μ) (c := (1 - p) * A))
            (hXi.mul_const A)]
        _ = (1 - p) * A := by
          simp [integral_const, integral_mul_const, hmean_int]
    have hi2 : (∫ ω, (X ω + p) * B ∂μ) = p * B := by
      calc
        _ = ∫ ω, (X ω * B + p * B) ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with ω
          ring
        _ = (∫ ω, X ω * B ∂μ) + (∫ ω, p * B ∂μ) := by
          rw [integral_add (hXi.mul_const B)
            (integrable_const (μ := μ) (c := p * B))]
        _ = p * B := by
          simp [integral_const, integral_mul_const, hmean_int]
    change (∫ ω, Real.exp (coeff * X ω) ∂μ) = twoPointMGF p coeff
    calc
      _ = ∫ ω, (1 - p - X ω) * A + (X ω + p) * B ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [hpoint]
      _ = (1 - p) * A + p * B := by
        rw [integral_add h1 h2, hi1, hi2]
      _ = twoPointMGF p coeff := by
        simp [A, B, twoPointMGF]
  refine ⟨hexp coeff, hpos, hmgf, ?_⟩
  simp [twoPointCGF, hmgf]

private theorem twoPointMGF_factor (p x : ℝ) :
    twoPointMGF p x =
      Real.exp (x * (-p)) * ((1 : ℝ) - p + p * Real.exp x) := by
  unfold twoPointMGF
  rw [show x * (1 - p) = x * (-p) + x by ring, Real.exp_add]
  ring

private lemma cgf_denominator_positive (p t : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : 0 < 1 - p + p * Real.exp t := by
  have he := Real.exp_pos t
  by_cases h : p = 0
  · simp [h]
  · have hp : 0 < p := lt_of_le_of_ne hp0 (Ne.symm h)
    have hm : 0 < p * Real.exp t := mul_pos hp he
    linarith

private lemma two_point_cgf_denominator_pos (p coeff : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 < (1 : ℝ) - p + p * Real.exp coeff := by
  exact cgf_denominator_positive p coeff hp0 hp1

private lemma derivative_bridge (f : ℝ → ℝ) (x d : ℝ) (hd : HasDerivAt f d x) : IsRealDerivative f x d := by
  have ht := (hasDerivAt_iff_tendsto_slope_zero).mp hd
  rw [Metric.tendsto_nhdsWithin_nhds] at ht
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := ht ε hε
  refine ⟨δ, hδ, ?_⟩
  intro h hh hsmall
  have hn : h ≠ 0 := by simpa using (ne_of_gt hh)
  have hb := hbound (by simpa using hn) (by simpa [dist_eq_norm, Real.norm_eq_abs] using hsmall)
  simpa [div_eq_inv_mul, mul_comm, dist_eq_norm, Real.norm_eq_abs] using hb

private lemma slope_derivative (p t : ℝ) (h : 0 < 1-p+p*Real.exp t) : HasDerivAt (cgfSlope p) (cgfCurvature p t) t := by
  have hn := (Real.hasDerivAt_exp t).const_mul p
  have hd := hn.const_add (1-p)
  have hh := (hn.div hd (ne_of_gt h)).sub_const p
  have he : (p * Real.exp t * (1-p+p*Real.exp t) - p*Real.exp t*(p*Real.exp t)) / (1-p+p*Real.exp t)^2 = cgfCurvature p t := by
    unfold cgfCurvature
    congr 1
    ring
  simpa only [cgfSlope, zero_add, he] using hh

private lemma quadratic_upper_bound (f g c : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : ∀ x, HasDerivAt g (c x) x)
    (hc : ∀ x, c x ≤ 1 / 4) (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (t : ℝ) : f t ≤ t ^ 2 / 8 := by
  have hG : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y / 4 - g y) (1 / 4 - c x) x := by
    intro x
    have hi := (hasDerivAt_id x).div_const (4 : ℝ)
    convert hi.sub (hg x) using 1 <;> simp [id] <;> ring
  have hmono : MonotoneOn (fun x : ℝ => x / 4 - g x) Set.univ := by
    apply monotoneOn_of_deriv_nonneg convex_univ
    · intro x hx
      exact (hG x).continuousAt.continuousWithinAt
    · intro x hx
      exact (hG x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hG x).deriv]
      exact sub_nonneg.mpr (hc x)
  have hF : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y ^ 2 / 8 - f y) (x / 4 - g x) x := by
    intro x
    have hp : HasDerivAt (fun y : ℝ => y ^ 2 / 8) (x / 4) x := by
      convert (((hasDerivAt_id x).pow 2).div_const (8 : ℝ)) using 1 <;> simp [id] <;> ring
    exact hp.sub (hf x)
  have hpos : MonotoneOn (fun x : ℝ => x ^ 2 / 8 - f x) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro x hx
      exact (hF x).continuousAt.continuousWithinAt
    · intro x hx
      exact (hF x).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx0 : 0 ≤ x := Set.mem_Ici.mp (interior_subset hx)
      have hh := hmono (by simp) (by simp) hx0
      rw [(hF x).deriv]
      have hz : (0 : ℝ) / 4 - g 0 = 0 := by simp [hg0]
      linarith
  have hneg : AntitoneOn (fun x : ℝ => x ^ 2 / 8 - f x) (Set.Iic 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Iic 0)
    · intro x hx
      exact (hF x).continuousAt.continuousWithinAt
    · intro x hx
      exact (hF x).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx0 : x ≤ 0 := Set.mem_Iic.mp (interior_subset hx)
      have hh := hmono (by simp) (by simp) hx0
      rw [(hF x).deriv]
      have hz : (0 : ℝ) / 4 - g 0 = 0 := by simp [hg0]
      linarith
  by_cases ht : 0 ≤ t
  · have hh := hpos (show (0 : ℝ) ∈ Set.Ici 0 by simp) (show t ∈ Set.Ici 0 by simpa [Set.mem_Ici] using ht) ht
    simp only [hf0, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div, sub_zero] at hh
    linarith
  · have ht' : t ≤ 0 := le_of_not_ge ht
    have hh := hneg (show t ∈ Set.Iic 0 by simpa [Set.mem_Iic] using ht') (show (0 : ℝ) ∈ Set.Iic 0 by simp) ht'
    simp only [hf0, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div, sub_zero] at hh
    linarith

/-- Part (b): actual first and second derivatives, their bound, and the CGF bound. -/
theorem two_point_cgf_calculus
    (p : ℝ) (hp0 : (0 : ℝ) ≤ p) (hp1 : p ≤ (1 : ℝ)) :
    twoPointCGF p (0 : ℝ) = (0 : ℝ) ∧
      cgfSlope p (0 : ℝ) = (0 : ℝ) ∧
      IsRealDerivative (twoPointCGF p) (0 : ℝ) (0 : ℝ) ∧
      ∀ coeff : ℝ,
        (0 : ℝ) < twoPointMGF p coeff ∧
        (0 : ℝ) < ((1 : ℝ) - p + p * Real.exp coeff) ∧
        twoPointCGF p coeff =
          Real.log ((1 : ℝ) - p + p * Real.exp coeff) - p * coeff ∧
        IsRealDerivative (twoPointCGF p) coeff (cgfSlope p coeff) ∧
        IsRealDerivative (cgfSlope p) coeff (cgfCurvature p coeff) ∧
        cgfCurvature p coeff ≤ (1 : ℝ) / (4 : ℝ) ∧
        twoPointCGF p coeff ≤ coeff ^ (2 : ℕ) / (8 : ℝ) := by
  have hden : ∀ t : ℝ, 0 < 1 - p + p * Real.exp t :=
    fun t => two_point_cgf_denominator_pos p t hp0 hp1
  have hmgf : ∀ t : ℝ, 0 < twoPointMGF p t := by
    intro t
    rw [twoPointMGF_factor]
    exact mul_pos (Real.exp_pos _) (hden t)
  have hlog : ∀ t : ℝ, twoPointCGF p t = Real.log (1 - p + p * Real.exp t) - p * t := by
    intro t
    unfold twoPointCGF
    rw [twoPointMGF_factor, Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt (hden t)), Real.log_exp]
    ring
  have hf : ∀ t : ℝ, HasDerivAt (twoPointCGF p) (cgfSlope p t) t := by
    intro t
    have hd := (((hasDerivAt_const t (1-p)).add ((hasDerivAt_const t p).mul (Real.hasDerivAt_exp t))).log (ne_of_gt (hden t))).sub ((hasDerivAt_const t p).mul (hasDerivAt_id t))
    have heq : twoPointCGF p = (fun x => Real.log (1-p+p*Real.exp x)-p*x) := funext hlog
    rw [heq]
    convert hd using 1 <;> simp [cgfSlope]
  refine ⟨?_, ?_, ?_, fun t => ⟨hmgf t, hden t, hlog t, derivative_bridge _ _ _ (hf t), ?_, ?_, ?_⟩⟩
  · simp [twoPointCGF, twoPointMGF]
  · simp [cgfSlope]
  · exact derivative_bridge _ _ _ (by simpa [cgfSlope] using hf 0)
  · exact derivative_bridge _ _ _ (slope_derivative p t (hden t))
  · unfold cgfCurvature
    rw [div_le_iff₀ (sq_pos_of_pos (hden t))]
    nlinarith [sq_nonneg ((1 - p) - p * Real.exp t)]
  · apply quadratic_upper_bound (fun x => twoPointCGF p x) (fun x => cgfSlope p x)
      (fun x => cgfCurvature p x) hf
      (fun x => slope_derivative p x (hden x))
      (fun x => by
        unfold cgfCurvature
        rw [div_le_iff₀ (sq_pos_of_pos (hden x))]
        nlinarith [sq_nonneg ((1 - p) - p * Real.exp x)])
      (by simp [twoPointCGF, twoPointMGF])
      (by simp [cgfSlope]) t

/-- The stated bound, for every real coefficient and every pointwise bounded random variable. -/
theorem hoeffding_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (a b : ℝ)
    (hX : Measurable X)
    (hX_mem : ∀ ω : Ω, a ≤ X ω ∧ X ω ≤ b) :
    ∀ coeff : ℝ,
      expectation μ
        (fun ω : Ω => Real.exp (coeff * (X ω - expectation μ X))) ≤
        Real.exp (coeff ^ (2 : ℕ) * (b - a) ^ (2 : ℕ) / (8 : ℝ)) := by
  intro coeff
  by_cases hab : a = b
  · subst b
    rcases degenerate_interval μ X a hX hX_mem with ⟨hmean, hexp⟩
    rw [show a - a = 0 by ring]
    simpa using (hexp coeff).le
  · have hlt : a < b := by
      exact lt_of_le_of_ne (by
        apply le_of_not_gt
        intro hba
        have hempty : (Set.univ : Set Ω) = ∅ := by
          ext ω
          have hh := hX_mem ω
          exact False.elim (not_lt_of_ge hh.2 (lt_of_lt_of_le hba hh.1))
        have hprob : μ (Set.univ : Set Ω) = 1 := measure_univ
        rw [hempty] at hprob
        simp at hprob) hab
    rcases normalized_two_point_reduction μ X a b hX hX_mem hlt with
      ⟨hp0, hp1, hY, hYi, hYmean, hspan, hYbound, hmgf, hscale⟩
    rcases two_point_cgf_calculus ((expectation μ X - a) / (b - a)) hp0 hp1 with
      ⟨_, _, _, hcgf_all⟩
    rcases hcgf_all (coeff * (b - a)) with
      ⟨hmgf_pos, _, _, _, _, _, hcgf_le⟩
    calc
      expectation μ (fun ω => Real.exp (coeff * (X ω - expectation μ X))) =
          expectation μ (fun ω => Real.exp (coeff * (b - a) * ((X ω - expectation μ X) / (b - a)))) := hscale coeff
      _ ≤ twoPointMGF ((expectation μ X - a) / (b - a)) (coeff * (b - a)) := (hmgf (coeff * (b - a))).2
      _ = Real.exp (twoPointCGF ((expectation μ X - a) / (b - a)) (coeff * (b - a))) := by
        rw [twoPointCGF]
        rw [Real.exp_log hmgf_pos]
      _ ≤ Real.exp ((coeff * (b - a)) ^ 2 / 8) := by
        exact Real.exp_le_exp.mpr hcgf_le
      _ = Real.exp (coeff ^ 2 * (b - a) ^ 2 / 8) := by ring_nf

end HoeffdingSignatures
