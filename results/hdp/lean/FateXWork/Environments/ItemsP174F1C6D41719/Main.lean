import Mathlib

open MeasureTheory ProbabilityTheory

theorem abstract_valued_random_variables
    {Ω 𝓧 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝓧]
    {n : ℕ} (X : Fin n → Ω → 𝓧) (f : (Fin n → 𝓧) → ℝ)
    (hX : ∀ i : Fin n, Measurable (X i))
    (hf : Measurable f) :
    Measurable (fun ω : Ω => f (fun i : Fin n => X i ω)) := by
  apply hf.comp
  exact measurable_pi_lambda _ hX
