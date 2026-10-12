import Mathlib

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace BoundedFourthMoment

/-- Mutual independence via factorization of finite coordinate events. -/
def IndependentCoordinates
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (n : ℕ) (X : Fin n → Ω → ℝ) : Prop :=
  ∀ (s : Finset (Fin n)) (B : Fin n → Set ℝ),
    (∀ (i : Fin n), MeasurableSet (B i)) →
    μ {ω : Ω | ∀ (i : Fin n), i ∈ s → X i ω ∈ B i} =
      (∏ i ∈ s, μ (X i ⁻¹' B i) : ENNReal)

/-- The source's Euclidean norm. -/
def euclideanNorm (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  RCLike.sqrt (∑ i : Fin n, (x i) ^ 2 : ℝ)

/-- The Euclidean length at each outcome. -/
def randomLength
    {Ω : Type*} (n : ℕ) (X : Fin n → Ω → ℝ) : Ω → ℝ :=
  fun ω => euclideanNorm n (fun (i : Fin n) => X i ω)

/-- Variance as the expectation of the squared centered variable. -/
def realVariance
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Ω → ℝ) : ℝ :=
  ∫ ω, (Y ω - (∫ η, Y η ∂μ)) ^ 2 ∂μ

private theorem fourth_moment_nonneg {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Y : Ω → ℝ) (h : Integrable (fun ω => Y ω ^ 4) μ) : 0 ≤ ∫ ω, Y ω ^ 4 ∂μ := by
  exact integral_nonneg (fun ω => by positivity)

private theorem randomLength_sq_eq_sum {Ω : Type*} (n : ℕ) (X : Fin n → Ω → ℝ) (ω : Ω) :
    (randomLength n X ω) ^ 2 = ∑ i : Fin n, (X i ω) ^ 2 := by
  simp [randomLength, euclideanNorm, Real.sq_sqrt, Finset.sum_nonneg fun i _ => sq_nonneg (X i ω)]

private lemma variance_randomLength_nonneg
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (n : ℕ) (X : Fin n → Ω → ℝ) :
    0 ≤ realVariance μ (randomLength n X) := by
  unfold realVariance
  exact integral_nonneg (fun ω => sq_nonneg _)

theorem variance_and_mean_bounds
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 0 < n) (K : ℝ) (X : Fin n → Ω → ℝ)
    (h_measurable : ∀ (i : Fin n), Measurable (X i))
    (h_independent : IndependentCoordinates μ n X)
    (h_second_moment :
      ∀ (i : Fin n), (∫ ω, (X i ω) ^ 2 ∂μ) = (1 : ℝ))
    (h_fourth_integrable :
      ∀ (i : Fin n), Integrable (fun ω => (X i ω) ^ 4) μ)
    (h_fourth_moment :
      ∀ (i : Fin n), (∫ ω, (X i ω) ^ 4 ∂μ) ≤ K ^ 4) :
    realVariance μ (randomLength n X) ≤ K ^ 4 ∧
      RCLike.sqrt (n : ℝ) - K ^ 4 / RCLike.sqrt (n : ℝ) ≤
        (∫ ω, randomLength n X ω ∂μ) ∧
      (∫ ω, randomLength n X ω ∂μ) ≤ RCLike.sqrt (n : ℝ) := by sorry

end BoundedFourthMoment
