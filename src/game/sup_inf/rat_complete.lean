import data.real.basic

/- Axiom : archimPrinciple : ∀ x : ℝ, x > 0 →  ∃ n : ℕ, n > 0 ∧ (1/n : ℝ) < x
-/

/-
# Chapter 2 : Sup and Inf

## Level 12
-/

def bdd (X : set ℝ) := bdd_above X ∧ bdd_below X
def complete (X : set ℝ) := ∀ Y : set ℝ, Y.nonempty ∧ Y ⊆ X ∧ bdd Y → ∃ s i : ℝ, is_lub Y s ∧ is_glb Y i 
def embedded_rationals : set ℝ := {x : ℝ | ∃ y : ℚ, x = ↑y}

/- Lemma
The rational numbers are not complete.
-/
lemma not_complete_rationals : 
    ¬ complete embedded_rationals :=
begin
   sorry,
end
