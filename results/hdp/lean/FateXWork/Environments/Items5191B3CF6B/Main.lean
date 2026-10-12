import Mathlib

/-!
# Exercise 5.1: continuous, differentiable, and Lipschitz functions

The source's part (b) is false without a bounded-gradient hypothesis: the square function is a
counterexample. We state both that defect and the standard corrected implication.
-/

namespace FateXWork.Environments.Items5191B3CF6B

universe u v

/-- Source 5.1(a): every Lipschitz function is uniformly continuous.

Prover notes: use the standard uniform-continuity consequence of `LipschitzWith`; the constant-zero
case is included by Mathlib's formulation. -/
theorem lipschitz_uniformContinuous
    {α : Type u} {β : Type v} [PseudoEMetricSpace α] [PseudoEMetricSpace β]
    {K : NNReal} {f : α → β} (hf : LipschitzWith K f) :
    UniformContinuous f := by
  sorry

/-- Corrected form of source 5.1(b): a globally differentiable real-valued function whose Fréchet
derivative norm is bounded by `C` is `C`-Lipschitz.

Prover notes: apply the global mean-value inequality to the derivative bound along each segment.
For maps to `ℝ`, the operator norm of `fderiv ℝ f x` is the Euclidean gradient norm appearing in
the finite-dimensional source statement. -/
theorem lipschitzWith_of_differentiable_norm_fderiv_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {C : NNReal}
    (hf : Differentiable ℝ f)
    (hbound : ∀ x, ‖fderiv ℝ f x‖ ≤ (C : ℝ)) :
    LipschitzWith C f := by
  sorry

/-- Fidelity companion for source 5.1(b): its unqualified assertion is false even in dimension one.
There exists a differentiable real function that is not Lipschitz with any finite constant.

Prover notes: take `f x = x^2`. If it were `K`-Lipschitz, compare `0` and a positive input larger
than `K`; cancellation contradicts the resulting quadratic-versus-linear estimate. -/
theorem exists_differentiable_not_lipschitz :
    ∃ f : ℝ → ℝ, Differentiable ℝ f ∧ ∀ K : NNReal, ¬ LipschitzWith K f := by
  sorry

/-- Source 5.1(c): `x ↦ sqrt |x|` on `[-1,1]` is uniformly continuous but not Lipschitz.

Prover notes: continuity on the compact interval yields uniform continuity. For failure of every
Lipschitz bound, compare `0` with `t^2` for sufficiently small positive `t`; the quotient of output
distance by input distance is `1/t`. -/
theorem sqrt_abs_uniformContinuousOn_not_lipschitzOn :
    UniformContinuousOn (fun x : ℝ => Real.sqrt |x|) (Set.Icc (-1 : ℝ) 1) ∧
      ∀ K : NNReal, ¬ LipschitzOnWith K (fun x : ℝ => Real.sqrt |x|) (Set.Icc (-1 : ℝ) 1) := by
  sorry

/-- Source 5.1(d): absolute value on `[-1,1]` is Lipschitz but not differentiable on that interval.

Prover notes: the reverse triangle inequality gives the `1`-Lipschitz estimate. Differentiability
on the interval would in particular give a derivative at the interior point `0`, contradicting the
different left and right difference quotients. -/
theorem abs_lipschitzOn_not_differentiableOn :
    LipschitzOnWith 1 (fun x : ℝ => |x|) (Set.Icc (-1 : ℝ) 1) ∧
      ¬ DifferentiableOn ℝ (fun x : ℝ => |x|) (Set.Icc (-1 : ℝ) 1) := by
  sorry

end FateXWork.Environments.Items5191B3CF6B
