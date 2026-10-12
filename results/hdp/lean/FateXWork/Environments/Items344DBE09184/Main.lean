import Mathlib

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace L1BallRandomVector

abbrev Vector (n : ℕ) := Fin n → ℝ

def l1Norm {n : ℕ} (x : Vector n) : ℝ :=
  (∑ i : Fin n, |x i| : ℝ)

def ball (n : ℕ) (r : ℝ) : Set (Vector n) :=
  {x : Vector n | l1Norm x ≤ r}

def uniformBall (n : ℕ) (r : ℝ) : Measure (Vector n) :=
  ((volume : Measure (Vector n)) (ball n r))⁻¹ •
    (volume : Measure (Vector n)).restrict (ball n r)

def coordinateDensity (n : ℕ) (r : ℝ) (t : ℝ) : ℝ :=
  if |t| ≤ r then
    (n : ℝ) / ((2 : ℝ) * r) *
      ((1 : ℝ) - |t| / r) ^ (n - 1)
  else (0 : ℝ)

def isotropic {n : ℕ} (μ : Measure (Vector n)) : Prop :=
  (∀ i : Fin n,
    Integrable (fun x : Vector n => x i) μ ∧
    (∫ x : Vector n, x i ∂μ) = (0 : ℝ)) ∧
  (∀ i j : Fin n,
    Integrable (fun x : Vector n => x i * x j) μ ∧
    (∫ x : Vector n, x i * x j ∂μ) =
      (if i = j then (1 : ℝ) else (0 : ℝ)))

def isotropicRadius (n : ℕ) : ℝ :=
  Real.sqrt (((n : ℝ) + (1 : ℝ)) * ((n : ℝ) + (2 : ℝ)) / (2 : ℝ))

def projection {n : ℕ} (coeff x : Vector n) : ℝ :=
  (∑ i : Fin n, coeff i * x i : ℝ)

def scalarPsi2 {n : ℕ} (μ : Measure (Vector n))
    (Y : Vector n → ℝ) : ℝ :=
  sInf {s : ℝ |
    (0 : ℝ) < s ∧
    Integrable (fun x : Vector n => Real.exp ((Y x / s) ^ 2)) μ ∧
    (∫ x : Vector n, Real.exp ((Y x / s) ^ 2) ∂μ) ≤ (2 : ℝ)}

def vectorPsi2 {n : ℕ} (μ : Measure (Vector n)) : ℝ :=
  sSup {v : ℝ | ∃ coeff : Vector n,
    (∑ i : Fin n, (coeff i) ^ 2 : ℝ) = (1 : ℝ) ∧
    v = scalarPsi2 μ (projection coeff)}

 theorem first_coordinate_density
    (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : (0 : ℝ) < r)
    (μ : Measure (Vector n)) (hμ : μ = uniformBall n r) :
    Measure.map (fun x : Vector n => x (⟨0, hn⟩ : Fin n)) μ =
      (volume : Measure ℝ).withDensity
        (fun t : ℝ => ENNReal.ofReal (coordinateDensity n r t)) := by sorry

 theorem isotropic_radius_comparable
    (n : ℕ) (hn : 0 < n) :
    (0 : ℝ) < isotropicRadius n ∧
    (n : ℝ) / (2 : ℝ) ≤ isotropicRadius n ∧
    isotropicRadius n ≤ (2 : ℝ) * (n : ℝ) := by sorry

 theorem uniform_ball_isotropic
    (n : ℕ) (hn : 0 < n)
    (μ : Measure (Vector n))
    (hμ : μ = uniformBall n (isotropicRadius n)) :
    isotropic μ := by sorry

 theorem isotropic_ball_psi2_lower_bound :
    ∃ c : ℝ, (0 : ℝ) < c ∧
      ∀ (n : ℕ) (hn : 0 < n) (μ : Measure (Vector n)),
        μ = uniformBall n (isotropicRadius n) →
        vectorPsi2 μ > c * Real.sqrt (n : ℝ) := by sorry

end L1BallRandomVector
