import Mathlib

open scoped BigOperators

noncomputable section

namespace SparseRandomGraph

attribute [local instance] Classical.propDecidable

/-- An unordered pair of distinct labeled vertices, represented once. -/
abbrev Edge (n : ℕ) := {e : Fin n × Fin n // e.1 < e.2}

/-- A labeled simple graph represented by its edge-presence bits. -/
abbrev Outcome (n : ℕ) := Edge n → Bool

/-- The finite sample space has the discrete sigma-algebra. -/
instance outcomeMeasurableSpace (n : ℕ) : MeasurableSpace (Outcome n) := ⊤

/-- Product Bernoulli mass of a graph in G(n,p). -/
def graphMass (n : ℕ) (p : ℝ) (G : Outcome n) : ℝ :=
  (∏ e : Edge n, if G e = true then p else (1 : ℝ) - p : ℝ)

/-- Event probability as an exact finite sum of graph masses. -/
def eventProbability (n : ℕ) (p : ℝ) (event : Outcome n → Prop) : ℝ :=
  (∑ G : Outcome n, if event G then graphMass n p G else (0 : ℝ) : ℝ)

/-- The number of present edges incident to a vertex. -/
def degree (n : ℕ) (G : Outcome n) (v : Fin n) : ℕ :=
  ((Finset.univ : Finset (Edge n)).filter
    (fun e => (e.1.1 = v ∨ e.1.2 = v) ∧ G e = true)).card

/-- Maximum degree over the finite vertex set. -/
def maximumDegree (n : ℕ) (G : Outcome n) : ℕ :=
  (Finset.univ : Finset (Fin n)).sup (fun v : Fin n => degree n G v)

private theorem zero_probability_at_zero (a b : ℝ) (ha : 0 < a) :
    eventProbability 3 0 (fun G : Outcome 3 => a ≤ (maximumDegree 3 G : ℝ) ∧ (maximumDegree 3 G : ℝ) ≤ b) = 0 := by
  classical
  unfold eventProbability
  apply Finset.sum_eq_zero
  intro G hG
  by_cases h : ∃ e, G e = true
  · obtain ⟨e, he⟩ := h
    have hm : graphMass 3 0 G = 0 := by
      unfold graphMass
      apply Finset.prod_eq_zero (Finset.mem_univ e)
      simp [he]
    simp [hm]
  · have hg : ∀ e, G e ≠ true := by simpa using h
    have hd : maximumDegree 3 G = 0 := by
      simp [maximumDegree, degree, hg]
    simp [hd, not_le.mpr ha]

private theorem not_maximum_degree_bounds : ¬ (∃ (c c₁ c₂ : ℝ),
    (0 : ℝ) < c ∧ (0 : ℝ) < c₁ ∧ (0 : ℝ) < c₂ ∧
      ∀ (n : ℕ) (p d : ℝ),
        (3 : ℕ) ≤ n → (0 : ℝ) ≤ p → p ≤ (1 : ℝ) →
        d = ((n : ℝ) - (1 : ℝ)) * p →
        d ≤ c * (Real.log (n : ℝ)) ^ ((99 : ℝ) / (100 : ℝ)) →
        ((99 : ℝ) / (100 : ℝ)) ≤ eventProbability n p (fun G : Outcome n =>
          c₁ * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) ≤ (maximumDegree n G : ℝ) ∧
          (maximumDegree n G : ℝ) ≤ c₂ * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)))) := by
  rintro ⟨c, c₁, c₂, hc, hc₁, hc₂, hmain⟩
  have hlog : 0 < Real.log (Real.log (3 : ℝ)) := by
    apply Real.log_pos
    apply (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2
    exact Real.exp_one_lt_three
  have ha : 0 < c₁ * Real.log (3 : ℝ) / Real.log (Real.log (3 : ℝ)) := by
    exact div_pos (mul_pos hc₁ (Real.log_pos (by norm_num))) hlog
  have hh := hmain 3 0 0 (by norm_num) (by norm_num) (by norm_num) (by ring) (by positivity)
  have he : eventProbability 3 0 (fun G : Outcome 3 =>
      c₁ * Real.log (3 : ℝ) / Real.log (Real.log (3 : ℝ)) ≤ (maximumDegree 3 G : ℝ) ∧
      (maximumDegree 3 G : ℝ) ≤ c₂ * Real.log (3 : ℝ) / Real.log (Real.log (3 : ℝ))) = 0 :=
    zero_probability_at_zero _ _ ha
  convert he ▸ hh using 1 <;> norm_num

/-- The source assertion with its stated expected-degree condition unchanged. -/
theorem maximum_degree_bounds :
    ∃ (c c₁ c₂ : ℝ),
      (0 : ℝ) < c ∧ (0 : ℝ) < c₁ ∧ (0 : ℝ) < c₂ ∧
      ∀ (n : ℕ) (p d : ℝ),
        (3 : ℕ) ≤ n →
        (0 : ℝ) ≤ p → p ≤ (1 : ℝ) →
        d = ((n : ℝ) - (1 : ℝ)) * p →
        d ≤ c * (Real.log (n : ℝ)) ^ ((99 : ℝ) / (100 : ℝ)) →
        ((99 : ℝ) / (100 : ℝ)) ≤
          eventProbability n p (fun G : Outcome n =>
            c₁ * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) ≤
                (maximumDegree n G : ℝ) ∧
            (maximumDegree n G : ℝ) ≤
                c₂ * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) := by
  refine ⟨1, 1, 1, by norm_num, by norm_num, by norm_num, ?_⟩
  intro n p d hn hp hp1 hd hbound
  have hz := zero_probability_at_zero 1 1 (by norm_num)
  have hn := not_maximum_degree_bounds
  sorry

end SparseRandomGraph
