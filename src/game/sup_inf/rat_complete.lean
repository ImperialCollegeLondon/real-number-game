import data.real.basic

/-
# Chapter 3 : Sup and Inf

## Level 12

This proof will be easy now.
-/

def bdd (X : set ℝ) := bdd_above X ∧ bdd_below X
def complete (X : set ℝ) := ∀ Y : set ℝ, Y.nonempty ∧ Y ⊆ X ∧ bdd Y → ∃ s i : ℝ, is_lub Y s ∧ is_glb Y i 
def embedded_rationals : set ℝ := {x : ℝ | ∃ y : ℚ, x = ↑y}

/- Lemma
The rational numbers are not complete.

Need to complete the proof.
-/
lemma not_complete_rationals : 
    ¬ complete embedded_rationals :=
begin
   sorry,
end
