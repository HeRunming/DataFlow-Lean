import Mathlib

noncomputable section

open MeasureTheory
open scoped BigOperators

universe u

namespace AlmostOrthogonal

abbrev Vec (n : ℕ) := Fin n → ℝ

def dot {n : ℕ} (x y : Vec n) : ℝ :=
  (∑ i : Fin n, x i * y i : ℝ)

def euclideanNorm {n : ℕ} (x : Vec n) : ℝ :=
  Real.sqrt (∑ i : Fin n, (x i) ^ (2 : ℕ) : ℝ)

noncomputable def direction {n : ℕ} (x : Vec n) : Vec n :=
  @ite (Vec n) (x = (0 : Vec n)) (Classical.propDecidable _)
    (0 : Vec n) (fun i : Fin n => x i / euclideanNorm x)

/-- The Luxemburg psi_2 norm is at most K: every strictly larger
    positive scale has finite exponential second moment at most 2. -/
def ScalarPsi2Bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → ℝ) (K : ℝ) : Prop :=
  (0 : ℝ) ≤ K ∧
    ∀ (t : ℝ), K < t → (0 : ℝ) < t →
      Integrable (fun ω : Ω => Real.exp ((Z ω / t) ^ (2 : ℕ))) μ ∧
      (∫ ω : Ω, Real.exp ((Z ω / t) ^ (2 : ℕ)) ∂μ) ≤ (2 : ℝ)

/-- The vector psi_2 norm is the supremum over Euclidean unit projections. -/
def VectorPsi2Bound {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (μ : Measure Ω) (X : Ω → Vec n) (K : ℝ) : Prop :=
  (0 : ℝ) ≤ K ∧
    ∀ (v : Vec n), euclideanNorm v = (1 : ℝ) →
      ScalarPsi2Bound μ (fun ω : Ω => dot (X ω) v) K

/-- Independence expressed directly by factorization of measurable events. -/
def Independent {Ω A B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure Ω) (X : Ω → A) (Y : Ω → B) : Prop :=
  ∀ (s : Set A) (t : Set B), MeasurableSet s → MeasurableSet t →
    μ {ω : Ω | X ω ∈ s ∧ Y ω ∈ t} =
      μ {ω : Ω | X ω ∈ s} * μ {ω : Ω | Y ω ∈ t}

/-- Equality of distributions on all measurable sets. -/
def SameLaw {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (μ : Measure Ω) (X Y : Ω → A) : Prop :=
  ∀ (s : Set A), MeasurableSet s →
    μ {ω : Ω | X ω ∈ s} = μ {ω : Ω | Y ω ∈ s}

/-- Mutual independence of all coordinates, not merely pairwise independence. -/
def IndependentCoordinates {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (μ : Measure Ω) (X : Ω → Vec n) : Prop :=
  ∀ (s : Fin n → Set ℝ), (∀ i : Fin n, MeasurableSet (s i)) →
    μ {ω : Ω | ∀ i : Fin n, X ω i ∈ s i} =
      (∏ i : Fin n, μ {ω : Ω | X ω i ∈ s i} : ENNReal)

/-- Finite first and second moments, mean zero, and variance one. -/
def StandardCoordinates {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (μ : Measure Ω) (X : Ω → Vec n) : Prop :=
  ∀ i : Fin n,
    Integrable (fun ω : Ω => X ω i) μ ∧
    Integrable (fun ω : Ω => (X ω i) ^ (2 : ℕ)) μ ∧
    (∫ ω : Ω, X ω i ∂μ) = (0 : ℝ) ∧
    (∫ ω : Ω, (X ω i) ^ (2 : ℕ) ∂μ) = (1 : ℝ)

/-- Isotropy means E[XXᵀ] = I; no additional mean-zero condition is imposed. -/
def Isotropic {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (μ : Measure Ω) (X : Ω → Vec n) : Prop :=
  ∀ (i j : Fin n),
    Integrable (fun ω : Ω => X ω i * X ω j) μ ∧
    (∫ ω : Ω, X ω i * X ω j ∂μ) =
      (if i = j then (1 : ℝ) else (0 : ℝ))

/-- Part (a): the constant depends only on the coordinate psi_2 bound. -/
theorem part_a (K : ℝ) (hK : (0 : ℝ) ≤ K) :
    ∃ (C : ℝ), (0 : ℝ) < C ∧
      ∀ (n : ℕ), 0 < n →
      ∀ (Ω : Type u) [MeasurableSpace Ω]
        (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X η : Ω → Vec n),
        Measurable X →
        Measurable η →
        IndependentCoordinates μ X →
        StandardCoordinates μ X →
        (∀ i : Fin n,
          ScalarPsi2Bound μ (fun ω : Ω => X ω i) K) →
        Independent μ (fun ω : Ω => direction (X ω)) η →
        SameLaw μ (fun ω : Ω => direction (X ω)) η →
        μ {ω : Ω |
          |dot (direction (X ω)) (η ω)| ≤
            C / Real.sqrt (n : ℝ)} ≥
          (99 / 100 : ENNReal) := by sorry

/-- Part (b): on a canonical joint sample space, the two projections
    provide the required independent, identically distributed vectors. -/
theorem part_b :
    ∃ (C : ℝ), (0 : ℝ) < C ∧
      ∀ (n : ℕ), 0 < n →
      ∃ (μ : Measure (Vec n × Vec n)),
        IsProbabilityMeasure μ ∧
        Measurable (fun ω : Vec n × Vec n => ω.1) ∧
        Measurable (fun ω : Vec n × Vec n => ω.2) ∧
        Independent μ
          (fun ω : Vec n × Vec n => ω.1)
          (fun ω : Vec n × Vec n => ω.2) ∧
        SameLaw μ
          (fun ω : Vec n × Vec n => ω.1)
          (fun ω : Vec n × Vec n => ω.2) ∧
        Isotropic μ (fun ω : Vec n × Vec n => ω.1) ∧
        Isotropic μ (fun ω : Vec n × Vec n => ω.2) ∧
        VectorPsi2Bound μ (fun ω : Vec n × Vec n => ω.1) C ∧
        VectorPsi2Bound μ (fun ω : Vec n × Vec n => ω.2) C ∧
        μ {ω : Vec n × Vec n | ω.1 = ω.2} ≥
          (99 / 100 : ENNReal) := by sorry

end AlmostOrthogonal
