import Mathlib

open MeasureTheory

noncomputable section

/-- The canonical normalized surface probability measure on the unit sphere. -/
def sphereUniformMeasure (n : ℕ) : Measure (EuclideanSpace ℝ (Fin n)) :=
  Measure.map
    (fun z : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      (z : EuclideanSpace ℝ (Fin n)))
    (Measure.toSphere (volume : Measure (EuclideanSpace ℝ (Fin n))))

/-- The radial probability measure with density `n * x^(n-1)` on `[0,1]`. -/
def radialMeasure (n : ℕ) : Measure ℝ :=
  Measure.withDensity volume (fun x : ℝ =>
    if 0 ≤ x ∧ x ≤ 1 then
      ENNReal.ofReal ((n : ℝ) * x ^ (n - 1))
    else
      0)

/-- Uniform probability measure on the Euclidean unit ball. -/
def IsUniformOnEuclideanBall
    {n : ℕ}
    (ν : Measure (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ t : Set (EuclideanSpace ℝ (Fin n)),
    MeasurableSet t →
      ν t =
        volume (t ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) /
          volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)

/-- Uniform law on the unit sphere, represented by normalized surface measure. -/
def IsUniformOnUnitSphere
    {n : ℕ}
    (ν : Measure (EuclideanSpace ℝ (Fin n))) : Prop :=
  ν = sphereUniformMeasure n

theorem exists_uniform_ball_radial_spherical_decomposition
    (n : ℕ)
    (hn : 1 ≤ n)
    (Ω : Type*)
    [MeasurableSpace Ω]
    (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (X : Ω → EuclideanSpace ℝ (Fin n))
    (hX_measurable : Measurable X)
    (hX_uniform : IsUniformOnEuclideanBall (Measure.map X μ)) :
    ∃ r : Ω → ℝ, ∃ Z : Ω → EuclideanSpace ℝ (Fin n),
      Measurable r ∧
      Measurable Z ∧
      (∀ᵐ ω ∂μ, 0 ≤ r ω ∧ r ω ≤ 1) ∧
      (∀ᵐ ω ∂μ, Z ω ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) ∧
      Measure.map r μ = radialMeasure n ∧
      IsUniformOnUnitSphere (Measure.map Z μ) ∧
      Measure.map (fun ω : Ω => (r ω, Z ω)) μ =
        (Measure.map r μ).prod (Measure.map Z μ) ∧
      (∀ᵐ ω ∂μ, X ω = r ω • Z ω) := by
  sorry
