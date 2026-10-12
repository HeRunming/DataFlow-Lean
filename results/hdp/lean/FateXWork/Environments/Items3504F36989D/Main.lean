import Mathlib

open BigOperators

namespace SeparateConvexity

def InCube {n : ℕ} (x : Fin n → ℝ) : Prop :=
  ∀ i : Fin n, (-1 : ℝ) ≤ x i ∧ x i ≤ (1 : ℝ)

def IsCubeVertex {n : ℕ} (x : Fin n → ℝ) : Prop :=
  ∀ i : Fin n, x i = (-1 : ℝ) ∨ x i = (1 : ℝ)

def SeparatelyConvexOnCube {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ (x : Fin n → ℝ), InCube x →
    ∀ (i : Fin n) (a b coeff : ℝ),
      (-1 : ℝ) ≤ a → a ≤ (1 : ℝ) →
      (-1 : ℝ) ≤ b → b ≤ (1 : ℝ) →
      (0 : ℝ) ≤ coeff → coeff ≤ (1 : ℝ) →
      f (Function.update x i (coeff * a + ((1 : ℝ) - coeff) * b)) ≤
        coeff * f (Function.update x i a) +
          ((1 : ℝ) - coeff) * f (Function.update x i b)

def ConvexOnCube {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ (x y : Fin n → ℝ), InCube x → InCube y →
    ∀ (coeff : ℝ), (0 : ℝ) ≤ coeff → coeff ≤ (1 : ℝ) →
      f (fun i : Fin n => coeff * x i + ((1 : ℝ) - coeff) * y i) ≤
        coeff * f x + ((1 : ℝ) - coeff) * f y

theorem separately_convex_not_convex_example :
    SeparatelyConvexOnCube
      (fun x : Fin 2 → ℝ => x (0 : Fin 2) * x (1 : Fin 2)) ∧
    ¬ ConvexOnCube
      (fun x : Fin 2 → ℝ => x (0 : Fin 2) * x (1 : Fin 2)) := by sorry

theorem separately_convex_attains_max_at_cube_vertex
    {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hsep : SeparatelyConvexOnCube f) :
    ∃ v : Fin n → ℝ, InCube v ∧ IsCubeVertex v ∧
      ∀ x : Fin n → ℝ, InCube x → f x ≤ f v := by sorry

end SeparateConvexity

namespace QuadraticGrothendieck

def DiagonalFree {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i : Fin n, A i i = (0 : ℝ)

/-- The normalized real Grothendieck inequality, uniformly over all finite
rectangular matrices and all finite-dimensional real unit vectors. -/
def IsGrothendieckConstant (K : ℝ) : Prop :=
  ∀ (m n d : ℕ) (B : Matrix (Fin m) (Fin n) ℝ),
    (∀ (x : Fin m → ℝ) (y : Fin n → ℝ),
      SeparateConvexity.IsCubeVertex x →
      SeparateConvexity.IsCubeVertex y →
      |((∑ i : Fin m, ∑ j : Fin n, B i j * x i * y j) : ℝ)| ≤ (1 : ℝ)) →
    ∀ (p : Fin m → Fin d → ℝ) (q : Fin n → Fin d → ℝ),
      (∀ i : Fin m,
        ((∑ k : Fin d, p i k * p i k) : ℝ) = (1 : ℝ)) →
      (∀ j : Fin n,
        ((∑ k : Fin d, q j k * q j k) : ℝ) = (1 : ℝ)) →
      |((∑ i : Fin m, ∑ j : Fin n,
        B i j * ((∑ k : Fin d, p i k * q j k) : ℝ)) : ℝ)| ≤ K

theorem quadratic_grothendieck
    (K : ℝ) (hK : IsGrothendieckConstant K)
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hdiag : DiagonalFree A)
    (hbound : ∀ x : Fin n → ℝ,
      SeparateConvexity.IsCubeVertex x →
      |((∑ i : Fin n, ∑ j : Fin n, A i j * x i * x j) : ℝ)| ≤ (1 : ℝ))
    {𝕜 : Type*} [RCLike 𝕜]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [CompleteSpace H]
    (u v : Fin n → H)
    (hu : ∀ i : Fin n, ‖u i‖ = (1 : ℝ))
    (hv : ∀ j : Fin n, ‖v j‖ = (1 : ℝ)) :
    ‖((∑ i : Fin n, ∑ j : Fin n,
      (algebraMap ℝ 𝕜 (A i j)) * inner 𝕜 (u i) (v j)) : 𝕜)‖ ≤
      (2 : ℝ) * K := by sorry

end QuadraticGrothendieck
