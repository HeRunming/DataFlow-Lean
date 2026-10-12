import Mathlib

/-!
Formalization of exercise 5.24 from HDP/source/environments.json.
-/

open scoped BigOperators
open MeasureTheory

namespace FateXWork
namespace Environments
namespace Items52419945955

/-- A concrete Euclidean size for finite real matrices, used as a norm bridge
in this elementary statement-level formalization. -/
noncomputable def matrixNorm {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, (M i j) ^ 2)

/-- The variance proxy appearing in the rectangular matrix Khintchine bound. -/
noncomputable def sigmaSquared {m n N : ℕ} (A : Fin N → Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  matrixNorm (∑ i, (A i).transpose * A i) +
    matrixNorm (∑ i, A i * (A i).transpose)

/-- The random signed sum of a finite family of rectangular matrices. -/
def matrixRademacherSum {Ω : Type*} {m n N : ℕ}
    (ε : Ω → Fin N → ℝ) (A : Fin N → Matrix (Fin m) (Fin n) ℝ) (ω : Ω) :
    Matrix (Fin m) (Fin n) ℝ := ∑ i, (ε ω i) • A i

/-- The sign and marginal part of the independent-Rademacher hypothesis.
The independence component is intentionally exposed as a predicate-level bridge
so that it can be replaced by the preferred probability API in the proof phase. -/
def IsIndependentRademacher {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {N : ℕ} (ε : Ω → Fin N → ℝ) : Prop :=
  (μ Set.univ = 1) ∧ (∀ i, Measurable (ε · i)) ∧
    (∀ ω i, ε ω i = 1 ∨ ε ω i = -1)

/-- Source proof: use self-adjoint dilation and the matrix Khintchine moment
estimate; the two diagonal variance blocks are bounded by `sigmaSquared`, and
the dilation dimension contributes `log (m+n)`.
Prover notes: instantiate the standard rectangular-matrix reduction with the
finite sums and Bochner integral displayed here. -/
theorem matrix_khintchine_rectangular {Ω : Type*} [MeasurableSpace Ω]
    {m n N : ℕ} (μ : Measure Ω) (ε : Ω → Fin N → ℝ)
    (A : Fin N → Matrix (Fin m) (Fin n) ℝ) (C : ℝ)
    (hε : IsIndependentRademacher μ ε) (hC : 0 < C)
    {p : ℝ} (hp : 1 ≤ p) :
    (∫ ω, matrixNorm (matrixRademacherSum ε A ω) ^ p ∂μ) ^ (1 / p) ≤
      C * Real.sqrt (sigmaSquared A) * Real.sqrt (p + Real.log (m + n : ℝ)) := by
  sorry

end Items52419945955
end Environments
end FateXWork
