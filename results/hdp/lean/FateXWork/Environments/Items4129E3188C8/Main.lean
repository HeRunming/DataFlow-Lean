import Mathlib

open scoped BigOperators

namespace SVDGeometry

/-- The real Euclidean inner product, expressed in coordinates. -/
def coordinateInner {d : ℕ} (x y : Fin d → ℝ) : ℝ :=
  (∑ k : Fin d, x k * y k : ℝ)

/-- The action of a real rectangular matrix on a coordinate vector. -/
def matrixAction {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℝ) : Fin m → ℝ :=
  fun k : Fin m => (∑ j : Fin n, A k j * x j : ℝ)

/-- An orthonormal family for the Euclidean inner product. -/
def CoordinateOrthonormal {r d : ℕ}
    (v : Fin r → (Fin d → ℝ)) : Prop :=
  ∀ i j : Fin r,
    coordinateInner (v i) (v j) =
      (if i = j then (1 : ℝ) else (0 : ℝ))

/-- Orthonormality together with reconstruction of every domain vector. -/
def CoordinateOrthonormalBasis {d : ℕ}
    (v : Fin d → (Fin d → ℝ)) : Prop :=
  CoordinateOrthonormal v ∧
    ∀ x : Fin d → ℝ, ∀ k : Fin d,
      x k = (∑ i : Fin d, coordinateInner (v i) x * v i k : ℝ)

/-- Equation (4.3) yields stretching in the right singular directions,
followed by an inner-product-preserving map to the left singular directions. -/
theorem stretch_then_rotate
    (m n : ℕ) (hmn : n ≤ m)
    (A : Matrix (Fin m) (Fin n) ℝ)
    (s : Fin n → ℝ)
    (v : Fin n → (Fin n → ℝ))
    (u : Fin n → (Fin m → ℝ))
    (hs : ∀ i : Fin n, (0 : ℝ) ≤ s i)
    (hv : CoordinateOrthonormalBasis v)
    (hu : CoordinateOrthonormal u)
    (h43 : ∀ i : Fin n,
      matrixAction A (v i) = (fun k : Fin m => s i * u i k)) :
    ∃ S : Matrix (Fin n) (Fin n) ℝ,
    ∃ R : Matrix (Fin m) (Fin n) ℝ,
      (∀ x : Fin n → ℝ, ∀ k : Fin n,
        matrixAction S x k =
          (∑ i : Fin n, s i * coordinateInner (v i) x * v i k : ℝ)) ∧
      (∀ i : Fin n,
        matrixAction S (v i) = (fun k : Fin n => s i * v i k)) ∧
      (∀ i : Fin n, matrixAction R (v i) = u i) ∧
      (∀ x y : Fin n → ℝ,
        coordinateInner (matrixAction R x) (matrixAction R y) =
          coordinateInner x y) ∧
      (∀ x : Fin n → ℝ,
        matrixAction A x = matrixAction R (matrixAction S x)) := by sorry

end SVDGeometry
