import Mathlib

 theorem random_process_identifies_with_random_vector
    (T : Set ℕ) (n : ℕ) (hT : T = Set.Icc (1 : ℕ) n)
    (Ω : Type*) [MeasurableSpace Ω]
    (X : ∀ t : T, Ω → ℝ)
    (hX : ∀ t : T, Measurable (X t))
    (e : T ≃ Fin n) :
    ∃ Y : Ω → (Fin n → ℝ),
      Measurable Y ∧
        ∀ (ω : Ω) (t : T), Y ω (e t) = X t ω := by
  use fun ω i => X (e.symm i) ω
  constructor
  · apply measurable_pi_iff.mpr
    intro i
    exact hX (e.symm i)
  · intro ω t
    exact congrArg (fun s => X s ω) (e.symm_apply_apply t)
