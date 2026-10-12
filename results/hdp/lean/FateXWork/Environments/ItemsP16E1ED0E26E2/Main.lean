import Mathlib.Analysis.Normed.Module.Convex

universe u

theorem norm_is_convex (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ConvexOn ℝ (Set.univ : Set E) (fun x : E => ‖x‖) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  calc
    ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
    _ = a • ‖x‖ + b • ‖y‖ := by
      simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]

theorem unit_ball_is_convex (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Convex ℝ {x : E | ‖x‖ ≤ (1 : ℝ)} := by
  simpa only [Metric.closedBall, dist_zero_right] using
    (convex_closedBall (0 : E) (1 : ℝ))
