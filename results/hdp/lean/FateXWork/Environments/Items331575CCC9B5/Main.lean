import Mathlib

open MeasureTheory
open scoped BigOperators

universe u

namespace RandomVectorSignatures

/-- Mutual independence expressed by factorization of finite intersections
of coordinate events. -/
def IndependentCoordinates
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) {n : ℕ} (X : Ω → Fin n → ℝ) : Prop :=
  ∀ (s : Finset (Fin n)) (A : Fin n → Set ℝ),
    (∀ i : Fin n, MeasurableSet (A i)) →
      μ {ω : Ω | ∀ i ∈ s, X ω i ∈ A i} =
        (∏ i ∈ s, μ {ω : Ω | X ω i ∈ A i})

/-- Isotropy in the Euclidean second-moment sense, with finiteness explicit. -/
def Isotropic
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) {n : ℕ} (X : Ω → Fin n → ℝ) : Prop :=
  ∀ coeff : Fin n → ℝ,
    Integrable
      (fun ω : Ω =>
        ((∑ i : Fin n, coeff i * X ω i : ℝ) ^ (2 : ℕ))) μ ∧
    (∫ ω : Ω,
        ((∑ i : Fin n, coeff i * X ω i : ℝ) ^ (2 : ℕ)) ∂μ) =
      (∑ i : Fin n, (coeff i) ^ (2 : ℕ) : ℝ)

private theorem indepFun_of_independentCoordinates
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (X : Ω → Fin n → ℝ)
    (h_independent : IndependentCoordinates μ X) (i j : Fin n) (hij : i ≠ j) :
    ProbabilityTheory.IndepFun (fun ω => X ω i) (fun ω => X ω j) μ := by
  rw [ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  have hji : j ≠ i := Ne.symm hij
  have h := h_independent ({i, j} : Finset (Fin n)) (fun k => if k = i then s else if k = j then t else Set.univ) (by
    intro k
    by_cases hki : k = i
    · simp [hki, hs]
    · by_cases hkj : k = j
      · simp [hkj, hji, ht]
      · simp [hki, hkj])
  simpa [Set.ext_iff, hji, hij, Finset.prod_insert, Finset.mem_singleton] using h

private theorem diagonal_second_moment
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (X : Ω → Fin n → ℝ)
    (h_variance_integrable : ∀ i : Fin n,
      Integrable (fun ω : Ω => (X ω i - (∫ η : Ω, X η i ∂μ)) ^ (2 : ℕ)) μ)
    (h_mean : ∀ i : Fin n, (∫ ω : Ω, X ω i ∂μ) = (0 : ℝ))
    (h_variance : ∀ i : Fin n,
      (∫ ω : Ω, (X ω i - (∫ η : Ω, X η i ∂μ)) ^ (2 : ℕ) ∂μ) = (1 : ℝ))
    (i : Fin n) :
    (∫ ω : Ω, X ω i * X ω i ∂μ) = 1 := by
  simpa [pow_two, h_mean i] using h_variance i

private theorem delta_sum
    {n : ℕ} (coeff : Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, coeff i * coeff j * if i = j then 1 else 0) =
      ∑ i : Fin n, coeff i ^ 2 := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · simp [pow_two]
  · intro j hj hji
    have hij : i ≠ j := Ne.symm hji
    simp [hij, hji]
  · simp

private theorem integrable_coord_sq_of_zero_mean
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (X : Ω → Fin n → ℝ)
    (h_variance_integrable : ∀ i : Fin n,
      Integrable (fun ω : Ω => (X ω i - (∫ η : Ω, X η i ∂μ)) ^ (2 : ℕ)) μ)
    (h_mean : ∀ i : Fin n, (∫ ω : Ω, X ω i ∂μ) = (0 : ℝ)) :
    ∀ i : Fin n, Integrable (fun ω : Ω => X ω i ^ 2) μ := by
  intro i
  have h := h_variance_integrable i
  rw [h_mean i] at h
  simpa only [sub_zero] using h

private theorem integral_double_sum_const_mul
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (n : ℕ) (X : Ω → Fin n → ℝ)
    (coeff : Fin n → ℝ)
    (hprod : ∀ i j : Fin n, Integrable (fun ω : Ω => X ω i * X ω j) μ) :
    (∫ ω : Ω, ∑ i : Fin n, ∑ j : Fin n,
          coeff i * coeff j * (X ω i * X ω j) ∂μ) =
        ∑ i : Fin n, ∑ j : Fin n, coeff i * coeff j * (∫ ω : Ω, X ω i * X ω j ∂μ) := by
  rw [integral_finset_sum]
  · congr 1
    funext i
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [integral_const_mul]
    · intro j hj
      exact (hprod i j).const_mul (coeff i * coeff j)
  · intro i hi
    apply integrable_finset_sum
    intro j hj
    exact (hprod i j).const_mul (coeff i * coeff j)

private theorem square_finset_sum_expand
    {n : ℕ} (coeff : Fin n → ℝ) (x : Fin n → ℝ) :
    (∑ i : Fin n, coeff i * x i) ^ 2 =
      ∑ i : Fin n, ∑ j : Fin n, coeff i * coeff j * (x i * x j) := by
  rw [pow_two]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Independent coordinates with zero mean and unit variance are isotropic. -/
theorem isotropic_of_independent_zero_mean_unit_variance
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (X : Ω → Fin n → ℝ)
    (h_measurable : ∀ i : Fin n, Measurable (fun ω : Ω => X ω i))
    (h_independent : IndependentCoordinates μ X)
    (h_integrable : ∀ i : Fin n, Integrable (fun ω : Ω => X ω i) μ)
    (h_mean : ∀ i : Fin n, (∫ ω : Ω, X ω i ∂μ) = (0 : ℝ))
    (h_variance_integrable : ∀ i : Fin n,
      Integrable
        (fun ω : Ω =>
          (X ω i - (∫ η : Ω, X η i ∂μ)) ^ (2 : ℕ)) μ)
    (h_variance : ∀ i : Fin n,
      (∫ ω : Ω,
        (X ω i - (∫ η : Ω, X η i ∂μ)) ^ (2 : ℕ) ∂μ) = (1 : ℝ)) :
    Isotropic μ X := by
  classical
  unfold Isotropic
  intro coeff
  have hsq := integrable_coord_sq_of_zero_mean μ n X h_variance_integrable h_mean
  have hprod : ∀ i j : Fin n, Integrable (fun ω : Ω => X ω i * X ω j) μ := by
    intro i j
    by_cases hij : i = j
    · subst j
      simpa only [pow_two] using hsq i
    · exact (indepFun_of_independentCoordinates μ n X h_independent i j hij).integrable_mul
        (h_integrable i) (h_integrable j)
  have hcross : ∀ i j : Fin n, (∫ ω : Ω, X ω i * X ω j ∂μ) = if i = j then 1 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      exact diagonal_second_moment μ n X h_variance_integrable h_mean h_variance i
    · rw [if_neg hij]
      rw [(indepFun_of_independentCoordinates μ n X h_independent i j hij).integral_fun_mul_eq_mul_integral
        (h_measurable i).aestronglyMeasurable (h_measurable j).aestronglyMeasurable]
      rw [h_mean i, h_mean j]
      norm_num
  constructor
  · have hdouble : Integrable
        (fun ω : Ω => ∑ i : Fin n, ∑ j : Fin n,
          coeff i * coeff j * (X ω i * X ω j)) μ := by
      apply integrable_finset_sum
      intro i hi
      apply integrable_finset_sum
      intro j hj
      exact (hprod i j).const_mul (coeff i * coeff j)
    convert hdouble using 1
    exact funext (fun ω => square_finset_sum_expand coeff (fun i => X ω i))
  · have hdouble := integral_double_sum_const_mul μ n X coeff hprod
    rw [show (∫ ω : Ω, (∑ i : Fin n, coeff i * X ω i) ^ 2 ∂μ) =
        (∫ ω : Ω, ∑ i : Fin n, ∑ j : Fin n,
          coeff i * coeff j * (X ω i * X ω j) ∂μ) by
      congr 1
      exact funext (fun ω => square_finset_sum_expand coeff (fun i => X ω i))]
    rw [hdouble]
    apply Eq.trans _ (delta_sum coeff)
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hcross i j]

end RandomVectorSignatures
