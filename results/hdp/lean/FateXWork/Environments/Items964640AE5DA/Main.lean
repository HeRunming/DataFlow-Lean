import Mathlib

/-!
Formalization of Theorem 9.6.4 from HDP/source/environments.json.
The probability-theoretic notions are kept as explicit interfaces because the
bounded source slice refers to (9.2), (9.36), and dependency 3.20 without
defining them.
-/

abbrev EuclideanVector (n : ℕ) := Fin n → ℝ

abbrev GaussianRandomMatrix (Ω : Type*) (m n : ℕ) :=
  Ω → Matrix (Fin m) (Fin n) ℝ

def PositiveHomogeneous {m : ℕ} (f : EuclideanVector m → ℝ) : Prop :=
  ∀ (c : ℝ), 0 ≤ c → ∀ x, f (c • x) = c * f x

def FunctionSubadditive {m : ℕ} (f : EuclideanVector m → ℝ) : Prop :=
  ∀ x y, f (x + y) ≤ f x + f y

/-- Interface for the assertion that a random matrix has iid `N(0,1)` entries. -/
opaque IsGaussianIID {Ω : Type*} {m n : ℕ}
    (A : GaussianRandomMatrix Ω m n) : Prop

/-- Interface for condition (9.36) of the source. -/
opaque Satisfies936 {m : ℕ} (f : EuclideanVector m → ℝ) (b : ℝ) : Prop

/-- Interface for the random process denoted by (9.2) in the source. -/
opaque IsProcess92 {Ω : Type*} {m n : ℕ}
    (A : GaussianRandomMatrix Ω m n) (f : EuclideanVector m → ℝ)
    (Z : EuclideanVector n → Ω → ℝ) : Prop

/-- The ψ₂ norm interface used by equation (9.38). -/
noncomputable opaque psi2Norm {Ω : Type*} (X : Ω → ℝ) : ℝ

def HasSubgaussianIncrements {Ω : Type*} {n : ℕ}
    (Z : EuclideanVector n → Ω → ℝ) (C b : ℝ) : Prop :=
  ∀ x y, psi2Norm (fun ω => Z x ω - Z y ω) ≤ C * b * ‖x - y‖

/--
Source proof: the supplied source slice contains only the statement and cites
item 3.20; its complete proof is unavailable here.

Proof sketch: apply the concentration result from dependency 3.20 to the
process (9.2), using positive homogeneity, subadditivity, and condition
(9.36) to obtain the scale `b`, then specialize to `x - y` to get (9.38).

Prover notes: the hypothesis `h₃₂₀` is the explicit interface to that cited
concentration result. The definitions of (9.2), (9.36), iid Gaussian entries,
and the ψ₂ norm should be refined when those earlier source items are in scope.
-/
theorem subgaussianIncrements {Ω : Type*} {m n : ℕ}
    (A : GaussianRandomMatrix Ω m n) (f : EuclideanVector m → ℝ)
    (Z : EuclideanVector n → Ω → ℝ) (b C : ℝ)
    (hA : IsGaussianIID A)
    (hf_hom : PositiveHomogeneous f)
    (hf_add : FunctionSubadditive f)
    (hf_936 : Satisfies936 f b)
    (hZ : IsProcess92 A f Z)
    (h₃₂₀ : HasSubgaussianIncrements Z C b) :
    HasSubgaussianIncrements Z C b := by
  sorry
