import Mathlib

noncomputable section

namespace CircleFrame

/-- The equally spaced points, with arbitrary initial angle, on the
origin-centered circle of the specified radius. -/
def circlePoint (N : ℕ) (θ : ℝ) (i : Fin N) : ℝ × ℝ :=
  let radius : ℝ := Real.sqrt ((2 : ℝ) / (N : ℝ))
  let angle : ℝ := θ + (2 : ℝ) * Real.pi * (i.val : ℝ) / (N : ℝ)
  (radius * Real.cos angle, radius * Real.sin angle)

/-- The Parseval identity for the ordinary Euclidean dot product on ℝ².
Coordinates are used explicitly to avoid the product type's default norm. -/
def IsParsevalFrame (N : ℕ) (v : Fin N → ℝ × ℝ) : Prop :=
  ∀ x : ℝ × ℝ,
    (∑ i : Fin N, ((x.1 * (v i).1 + x.2 * (v i).2) ^ (2 : ℕ) : ℝ)) =
      x.1 ^ (2 : ℕ) + x.2 ^ (2 : ℕ)

/-- Literal transcription on the positive-radius domain.
The source claim is false for N = 1 and N = 2; no additional lower
bound is silently inserted here. -/
theorem equispaced_circle_parseval
    (N : ℕ) (hN : 0 < N) (θ : ℝ) :
    IsParsevalFrame N (circlePoint N θ) := by sorry

end CircleFrame
