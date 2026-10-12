import Mathlib

namespace FateXWork.Environments.Items615A0DA0F42

/-- A finite random experiment intended to arise from uniformly assigning the
vertices of a finite graph to two sides; `cut` counts crossing edges. -/
structure RandomCutExperiment where
  Ω : Type
  finite_Ω : Fintype Ω
  nonempty_Ω : Nonempty Ω
  edgeCount : ℕ
  cut : Ω → ℕ

attribute [instance] RandomCutExperiment.finite_Ω

/-- Uniform probability on the finite sample space of a random-cut experiment. -/
noncomputable def uniformProbability (X : RandomCutExperiment) (P : X.Ω → Prop)
    [DecidablePred P] : ℝ :=
  ((Finset.univ.filter P).card : ℝ) / Fintype.card X.Ω

/-- The mean of the cut random variable under the uniform experiment. -/
noncomputable def uniformCutMean (X : RandomCutExperiment) : ℝ :=
  (∑ ω : X.Ω, (X.cut ω : ℝ)) / Fintype.card X.Ω

/-- Interface facts supplied by the concrete finite-graph/random-bipartition bridge.
This draft records the mean identity, while the concrete graph representation remains
an explicit scope item in the blueprint. -/
structure IsGraphRandomCut (X : RandomCutExperiment) : Prop where
  mean_eq_half : uniformCutMean X = (X.edgeCount : ℝ) / 2

/-- Source: Exercise 6.15, `HDP/source/environments.json:685`.

Source proof: expose the independent vertex-side choices and apply a
bounded-differences (Azuma--Hoeffding/McDiarmid) inequality to the cut.  Its
mean is `E / 2`; the subgaussian estimate yields the displayed exponential
bound for `s ≥ 1`.  A concrete finite-graph/bipartition bridge is still needed
for exact source coverage; see the scope change in the blueprint.
-/
theorem randomCut_exponentially_concentrated :
    ∃ c : ℝ, 0 < c ∧ ∀ (X : RandomCutExperiment), IsGraphRandomCut X →
      0 < X.edgeCount → ∀ s : ℝ, 1 ≤ s →
      uniformProbability X (fun ω =>
        |(X.cut ω : ℝ) - (X.edgeCount : ℝ) / 2| ≥
          s * Real.sqrt (X.edgeCount : ℝ)) ≤
        2 * Real.exp (-c * s) := by
  sorry

end FateXWork.Environments.Items615A0DA0F42
