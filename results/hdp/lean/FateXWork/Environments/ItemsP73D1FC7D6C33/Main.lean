import Mathlib

/--
Source proof: not applicable; the source entry is an informal definition.
Proof sketch: PCA is represented by its indexed principal components, the subspace
that they span, and a map sending data to that subspace.
Prover notes: the source does not specify an optimization criterion, orthogonality,
or a canonical projection, so these are intentionally not asserted here.
-/
structure PCA (Data V : Type*) [AddCommGroup V] [Module ℝ V] (n : ℕ) where
  components : Fin n → V
  subspace : Submodule ℝ V
  spans_components : subspace = Submodule.span ℝ (Set.range components)
  project : Data → subspace

/--
Source proof: not applicable; this records the source's follow-on visualization
condition for a two- or three-dimensional span.
Proof sketch: visualization is available exactly when the selected subspace has
finite dimension two or three.
Prover notes: `finrank` formalizes dimension over `ℝ`; the source supplies no
existence or visualization algorithm, so this is a predicate on an existing PCA.
-/
def PCA.visualizable {Data V : Type*} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} (p : PCA Data V n) : Prop :=
  FiniteDimensional ℝ p.subspace ∧
    (Module.finrank ℝ p.subspace = 2 ∨
      Module.finrank ℝ p.subspace = 3)
