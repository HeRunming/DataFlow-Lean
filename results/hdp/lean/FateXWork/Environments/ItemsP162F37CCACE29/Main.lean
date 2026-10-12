import Mathlib.Analysis.Matrix.Order

def succeq (X Y : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  Matrix.PosSemidef (X - Y)

theorem exists_incomparable_real_matrices :
    ∃ (X Y : Matrix (Fin 2) (Fin 2) ℝ),
      ¬ succeq X Y ∧ ¬ succeq Y X := by
  refine ⟨!![1, 0; 0, 0], !![0, 0; 0, 1], ?_, ?_⟩
  · intro h
    have h' := h.diag_nonneg (i := (1 : Fin 2))
    norm_num [succeq] at h'
  · intro h
    have h' := h.diag_nonneg (i := (0 : Fin 2))
    norm_num [succeq] at h'
