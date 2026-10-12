import Mathlib

/-!
Formalization of source item 8.3.8 from `HDP/source/environments.json`.
-/

abbrev BitString (n : Nat) := Fin n → Bool

def b001 : BitString 3 := ![true, false, false]
def b010 : BitString 3 := ![false, true, false]
def b100 : BitString 3 := ![false, false, true]
def b111 : BitString 3 := ![true, true, true]

/--
Source proof: the source gives this as a finite worked enumeration following the
Pajor-lemma proof: remove the third coordinate from Ω = {1,2,3}, then group the
four displayed binary words by that removed bit. Prover notes: unfold the
explicit words and discharge the finite-set equality by extensionality and
finite case analysis (for example, `decide` after suitable simplification).
-/
theorem example_8_3_8 :
    ({b001, b010, b100, b111} : Finset (BitString 3)) =
      ({b010, b100} : Finset (BitString 3)) ∪
        ({b001, b111} : Finset (BitString 3)) := by
  sorry
