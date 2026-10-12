import Mathlib

noncomputable section

open scoped BigOperators

namespace RandomPermutationCoordinates

/-- The random vector evaluated at a permutation. -/
def permutedVector {n : ℕ} (x : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) : Fin n → ℝ :=
  fun i => x (σ i)

/-- Expectation for the uniform distribution on all permutations. -/
def uniformMean {n : ℕ}
    (f : Equiv.Perm (Fin n) → ℝ) : ℝ :=
  (∑ σ : Equiv.Perm (Fin n), f σ : ℝ) /
    (Fintype.card (Equiv.Perm (Fin n)) : ℝ)

/-- Covariance for the same uniform distribution. -/
def uniformCovariance {n : ℕ}
    (f g : Equiv.Perm (Fin n) → ℝ) : ℝ :=
  uniformMean (fun σ =>
    (f σ - uniformMean f) * (g σ - uniformMean g))

def meanVector {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => uniformMean (fun σ => permutedVector x σ i)

def covarianceMatrix {n : ℕ} (x : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => uniformCovariance
    (fun σ => permutedVector x σ i)
    (fun σ => permutedVector x σ j)

/-- The given constraints exclude dimensions zero and one. -/
theorem admissible_dimension
    (n : ℕ) (x : Fin n → ℝ)
    (hzero : (∑ i : Fin n, x i : ℝ) = (0 : ℝ))
    (hunit : (∑ i : Fin n, (x i) ^ 2 : ℝ) = (1 : ℝ)) :
    2 ≤ n := by sorry

/-- Part (a): the mean vector and covariance matrix entries. -/
theorem mean_and_covariance
    (n : ℕ) (x : Fin n → ℝ)
    (hzero : (∑ i : Fin n, x i : ℝ) = (0 : ℝ))
    (hunit : (∑ i : Fin n, (x i) ^ 2 : ℝ) = (1 : ℝ)) :
    (∀ i : Fin n, meanVector x i = (0 : ℝ)) ∧
    (∀ i j : Fin n,
      covarianceMatrix x i j =
        if i = j then (1 : ℝ) / (n : ℝ)
        else -(1 : ℝ) / ((n : ℝ) * ((n : ℝ) - (1 : ℝ)))) := by sorry

/-- Part (b): positive variances and strictly negative off-diagonal covariances. -/
theorem negative_coordinate_covariances
    (n : ℕ) (x : Fin n → ℝ)
    (hzero : (∑ i : Fin n, x i : ℝ) = (0 : ℝ))
    (hunit : (∑ i : Fin n, (x i) ^ 2 : ℝ) = (1 : ℝ)) :
    (∀ i : Fin n, (0 : ℝ) < covarianceMatrix x i i) ∧
    (∀ i j : Fin n, i ≠ j → covarianceMatrix x i j < (0 : ℝ)) := by sorry

/-- Part (b): pointwise compensation underlying the heuristic explanation. -/
theorem pointwise_coordinate_compensation
    (n : ℕ) (x : Fin n → ℝ)
    (hzero : (∑ i : Fin n, x i : ℝ) = (0 : ℝ))
    (hunit : (∑ i : Fin n, (x i) ^ 2 : ℝ) = (1 : ℝ)) :
    ∀ σ : Equiv.Perm (Fin n),
      (∑ i : Fin n, permutedVector x σ i : ℝ) = (0 : ℝ) ∧
      (∀ i : Fin n,
        (∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
          permutedVector x σ j : ℝ) = -permutedVector x σ i) := by sorry

end RandomPermutationCoordinates
