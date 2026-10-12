import Mathlib

/-!
# Shared probability vocabulary

Authoritative definitions for the probabilistic objects that recur across the
HDP batches: the standard Gaussian law and densities, Gaussian width,
shattering, Rademacher variables, isotropy, and the `ψ₂` scale of sub-Gaussian
concentration.

## Namespace

Every declaration in this file lives in the namespace
`FateXWork.Shared.Probability`, nested under the common root
`FateXWork.Shared` shared by all domain modules (`FateXWork.Shared.Basic`,
`.Analysis`, `.Convexity`, `.LinearAlgebra`). The nesting is deliberate: 198 of
the batch sources declare their objects at the top level, so an un-namespaced
shared definition would collide with a batch definition of the same name as soon
as a batch imports this module. Namespacing keeps the shared vocabulary and the
batch vocabulary disjoint, so both compile side by side.

## Conventions

A random variable is always a plain function `Ω → ℝ` together with the measure
`μ` it is distributed by, passed as an explicit argument; definitions do not
install instances or depend on a `MeasureSpace` instance being in scope.

`psi2Norm` is valued in `ENNReal` rather than `ℝ`. The mathematical `ψ₂` norm
is an infimum of a set of radii that is empty for a variable that is not
sub-Gaussian, and `ENNReal` carries that value honestly as `⊤`, whereas an `ℝ`
codomain would silently report `0` for the empty set — the value a *concentrated*
variable has. `IsSubgaussian` is the corresponding finiteness predicate.
-/

open scoped BigOperators
open MeasureTheory

namespace FateXWork.Shared.Probability

/-- The standard Gaussian measure on `ℝⁿ`, the product of `n` copies of `N(0,1)`. -/
noncomputable def standardGaussianMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1

/-- The standard normal density `(1/√(2π)) · exp(-x²/2)` on `ℝ`. -/
noncomputable def standardNormalDensity (x : ℝ) : ℝ :=
  1 / Real.sqrt (2 * Real.pi) * Real.exp (-(x ^ 2) / 2)

/-- The `N(0, Iₙ)` density on `ℝⁿ` with respect to Lebesgue measure,
`(2π)^(-n/2) · exp(-‖x‖₂²/2)`. -/
noncomputable def standardGaussianDensity {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.exp (-(∑ i : Fin n, (x i) ^ 2) / 2) / (Real.sqrt (2 * Real.pi)) ^ n

/-- The class `F` shatters the finite set `s`: every subset of `s` is the trace of
a member of `F`. -/
def Shatters {X : Type*} (F : Set (Set X)) (s : Finset X) : Prop :=
  ∀ t : Finset X, t ⊆ s → ∃ H : Set X, H ∈ F ∧ H ∩ (↑s : Set X) = (↑t : Set X)

/-- The function-class form of shattering: every labelling of `s` is matched on
`s` by some member of `F`. -/
def ShattersFamily {X Y : Type*} (F : Set (X → Y)) (s : Finset X) : Prop :=
  ∀ g : X → Y, ∃ f ∈ F, ∀ x : X, x ∈ s → f x = g x

/-- Gaussian width: the expectation of `sup_{t ∈ T} ⟨g, t⟩` for `g ~ N(0, Iₙ)`.

For `T` bounded the supremum is finite; the definition is stated for arbitrary
`T`, where the inner supremum carries the usual `sSup` convention on `ℝ`. -/
noncomputable def gaussianWidth {n : ℕ} (T : Set (Fin n → ℝ)) : ℝ :=
  ∫ g : Fin n → ℝ, sSup ((fun t : Fin n → ℝ => ∑ i : Fin n, g i * t i) '' T)
    ∂(standardGaussianMeasure n)

/-- `X` is Rademacher: measurable, almost surely `±1`, with each sign carrying
mass `1/2`. The measure is intended to be a probability measure. -/
def IsRademacher {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) : Prop :=
  AEMeasurable X μ ∧
    (∀ᵐ ω ∂μ, X ω = (1 : ℝ) ∨ X ω = (-1 : ℝ)) ∧
    μ {ω | X ω = (1 : ℝ)} = (1 / 2 : ENNReal) ∧
    μ {ω | X ω = (-1 : ℝ)} = (1 / 2 : ENNReal)

/-- `t` is an admissible `ψ₂` radius for `X`: positive, with
`E exp((X/t)²) ≤ 2`. -/
def Psi2Admissible {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ)
    (t : ℝ) : Prop :=
  0 < t ∧
    Integrable (fun ω : Ω => Real.exp ((X ω / t) ^ 2)) μ ∧
    (∫ ω : Ω, Real.exp ((X ω / t) ^ 2) ∂μ) ≤ 2

/-- The `ψ₂` norm of `X`, the infimum of its admissible `ψ₂` radii, and `⊤` when
there are none. -/
noncomputable def psi2Norm {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) : ENNReal :=
  sInf {c : ENNReal | ∃ t : ℝ, Psi2Admissible μ X t ∧ c = ENNReal.ofReal t}

/-- `X` is sub-Gaussian under `μ`: it admits a finite `ψ₂` radius. No centring or
integrability of `X` itself is assumed. -/
def IsSubgaussian {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) : Prop :=
  ∃ t : ℝ, Psi2Admissible μ X t

/-- `X : Ω → ℝⁿ` is isotropic under the probability measure `μ`: its second
moments exist and its covariance matrix is the identity, `E[X i * X j] = δ i j`. -/
def Isotropic {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (μ : Measure Ω)
    (X : Ω → Fin n → ℝ) : Prop :=
  IsProbabilityMeasure μ ∧
    (∀ i j : Fin n, Integrable (fun ω : Ω => X ω i * X ω j) μ) ∧
    ∀ i j : Fin n, (∫ ω : Ω, X ω i * X ω j ∂μ) = if i = j then 1 else 0

/-- The standard normal density is strictly positive. -/
lemma standardNormalDensity_pos (x : ℝ) : 0 < standardNormalDensity x := by
  rw [standardNormalDensity]
  positivity

/-- The standard Gaussian density on `ℝⁿ` is strictly positive. -/
lemma standardGaussianDensity_pos {n : ℕ} (x : Fin n → ℝ) :
    0 < standardGaussianDensity x := by
  rw [standardGaussianDensity]
  positivity

end FateXWork.Shared.Probability
