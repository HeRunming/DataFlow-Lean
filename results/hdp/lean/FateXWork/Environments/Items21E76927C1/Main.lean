import Mathlib

open MeasureTheory
open ProbabilityTheory
open scoped BigOperators

private theorem half_pow_pos (n : ℕ) : (0 : ℝ) < (0.5 : ℝ) ^ n := by
  positivity

private theorem ninetyfive_pow_pos (n : ℕ) : (0 : ℝ) < (0.95 : ℝ) ^ n := by
  positivity

private theorem negate_power_checkpoint : (0.95 : ℝ) ^ 100 < (0.006 : ℝ) := by
  norm_num

private theorem product_uniform_probability_bounds_zero
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin 0 → Ω → ℝ)
    (h_measurable : ∀ i : Fin 0, Measurable (X i))
    (h_independent : ProbabilityTheory.iIndepFun X μ)
    (h_uniform : ∀ i : Fin 0,
      Measure.map (X i) μ =
        Measure.restrict MeasureTheory.volume (Set.Icc (0 : ℝ) (1 : ℝ)))
    (h_integrable : ∀ i : Fin 0, Integrable (X i) μ)
    (h_product_integrable :
      Integrable (fun ω : Ω => ∏ i : Fin 0, X i ω) μ) :
    (0.5 : ℝ) ^ 0 ≤
        (μ {ω : Ω |
          ∏ i : Fin 0, X i ω ≥
            ∫ ω : Ω, ∏ i : Fin 0, X i ω ∂μ}).toReal ∧
      (μ {ω : Ω |
          ∏ i : Fin 0, X i ω ≥
            ∫ ω : Ω, ∏ i : Fin 0, X i ω ∂μ}).toReal ≤
        (0.95 : ℝ) ^ 0 := by
  norm_num

private theorem uniform_restriction_mass_one :
    (Measure.restrict MeasureTheory.volume (Set.Icc (0 : ℝ) (1 : ℝ))) Set.univ = 1 := by
  simp

private theorem probability_measure_mass_univ
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] : μ Set.univ = 1 := by
  exact measure_univ

theorem product_uniform_probability_bounds
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ)
    (X : Fin n → Ω → ℝ)
    (h_measurable : ∀ i : Fin n, Measurable (X i))
    (h_independent : ProbabilityTheory.iIndepFun X μ)
    (h_uniform : ∀ i : Fin n,
      Measure.map (X i) μ =
        Measure.restrict MeasureTheory.volume (Set.Icc (0 : ℝ) (1 : ℝ)))
    (h_integrable : ∀ i : Fin n, Integrable (X i) μ)
    (h_product_integrable :
      Integrable (fun ω : Ω => ∏ i : Fin n, X i ω) μ) :
    (0.5 : ℝ) ^ n ≤
        (μ {ω : Ω |
          ∏ i : Fin n, X i ω ≥
            ∫ ω : Ω, ∏ i : Fin n, X i ω ∂μ}).toReal ∧
      (μ {ω : Ω |
          ∏ i : Fin n, X i ω ≥
            ∫ ω : Ω, ∏ i : Fin n, X i ω ∂μ}).toReal ≤
        (0.95 : ℝ) ^ n := by
  classical
  by_cases hn : n = 0
  · subst n
    norm_num
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hhalf : (0 : ℝ) < (0.5 : ℝ) ^ n := half_pow_pos n
    have hninetyfive : (0 : ℝ) < (0.95 : ℝ) ^ n := ninetyfive_pow_pos n
    /-
    Negative evidence:
    the normalization contradiction route is ruled out: the premises are
    consistent, since both μ univ and each pushed-forward marginal have mass
    one.  The canonical product model instead gives a genuine obstruction for
    large n.  With Y i = -log (X i), the event is
    {∑ i, Y i ≤ n * log 2}, and its probability is
      1 - exp (-n * log 2) * ∑ k in Finset.range n, (n * log 2)^k / k!.
    Its large-deviation rate is 1 - log 2 - log (1 / log 2), approximately
    0.0597, which is larger than -log 0.95, approximately 0.0513, so the
    probability is eventually smaller than 0.95^n.  Hence the stated upper
    bound is false for sufficiently large n under the standard independent
    uniform model.  Formalizing that counterexample requires substantial
    product-measure and incomplete-gamma infrastructure not present in this
    file; no contradiction can be derived from the abstract premises alone.
    -/
    have hcounter : (0.95 : ℝ) ^ 100 < (0.006 : ℝ) := negate_power_checkpoint
    have hmass := uniform_restriction_mass_one
    /-
    Negative evidence:
    `hcounter` is a kernel-checked numerical checkpoint, but it does not
    relate the event measure to the product model.  The assumptions do not
    imply `False`: `μ univ = 1` and the uniform restriction also has mass 1.
    Therefore neither `False.elim` nor `True.elim` can close this branch.
    A complete negation requires an explicit product-space countermodel and
    its gamma-CDF calculation, which is not expressible from the available
    hypotheses without adding substantial measure-theory infrastructure.
    -/
    sorry
