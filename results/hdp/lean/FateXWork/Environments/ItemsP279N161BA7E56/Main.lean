import Mathlib

theorem random_subspace_as_kernel
    (m n : ℕ)
    (Ω : Type*)
    (A : Ω → Matrix (Fin m) (Fin n) ℝ) :
    ∃ E : Ω → Submodule ℝ (Fin n → ℝ),
      ∀ ω : Ω, E ω = (A ω).mulVecLin.ker := by
  refine ⟨fun ω => (A ω).mulVecLin.ker, ?_⟩
  intro ω
  rfl
