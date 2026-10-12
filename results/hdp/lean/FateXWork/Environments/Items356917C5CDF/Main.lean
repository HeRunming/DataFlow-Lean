import Mathlib

open MeasureTheory
open scoped BigOperators

namespace GaussianSignCorrection

/-- Euclidean inner product in real coordinates. -/
def dot {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  (∑ i : Fin n, (x i * y i : ℝ) : ℝ)

/-- Coordinate inclusion of R^(n-1) into R^n by appending zero. -/
def pad {n : ℕ} (w : Fin (n - 1) → ℝ) : Fin n → ℝ :=
  fun i : Fin n =>
    if h : i.val < n - 1 then w ⟨i.val, h⟩ else (0 : ℝ)

/-- Pairing with a vector in the specified coordinate subspace. -/
def pairing {n : ℕ} (x : Fin n → ℝ) (w : Fin (n - 1) → ℝ) : ℝ :=
  dot x (pad w)

/-- Real sign, with value zero at zero. -/
noncomputable def realSign (t : ℝ) : ℝ :=
  if t > (0 : ℝ) then (1 : ℝ)
  else if t < (0 : ℝ) then (-1 : ℝ) else (0 : ℝ)

/-- Standard Gaussian law specified through every real linear projection. -/
def HasStandardGaussianLaw
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (g : Ω → (Fin n → ℝ)) : Prop :=
  AEMeasurable g μ ∧
    ∀ a : Fin n → ℝ,
      Measure.map (fun ω : Ω => dot (g ω) a) μ =
        ProbabilityTheory.gaussianReal (0 : ℝ)
          (Real.toNNReal (dot a a))

/-- The source's correction variable Z_w. -/
noncomputable def correction {n : ℕ}
    (x : Fin n → ℝ) (w : Fin (n - 1) → ℝ) : ℝ :=
  Real.sqrt ((2 : ℝ) / Real.pi) * pairing x w -
    realSign (pairing x w)

theorem part_a
    (n : ℕ) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → (Fin n → ℝ))
    (hg : HasStandardGaussianLaw μ g)
    (u v : Fin (n - 1) → ℝ)
    (hu : dot u u = (1 : ℝ))
    (hv : dot v v = (1 : ℝ)) :
    (∫ ω : Ω, pairing (g ω) u * realSign (pairing (g ω) v) ∂μ) =
      Real.sqrt ((2 : ℝ) / Real.pi) * dot u v := by sorry

theorem part_b
    (n : ℕ) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → (Fin n → ℝ))
    (hg : HasStandardGaussianLaw μ g)
    (u v : Fin (n - 1) → ℝ)
    (hu : dot u u = (1 : ℝ))
    (hv : dot v v = (1 : ℝ)) :
    (∫ ω : Ω,
      realSign (pairing (g ω) u) * realSign (pairing (g ω) v) ∂μ) =
      ((2 : ℝ) / Real.pi) * dot u v +
        (∫ ω : Ω, correction (g ω) u * correction (g ω) v ∂μ) := by sorry

end GaussianSignCorrection
