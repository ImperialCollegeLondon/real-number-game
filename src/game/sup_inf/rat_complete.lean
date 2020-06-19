import game.sup_inf.unbdd_iff
import data.real.basic

namespace xena -- hide

/-
# Chapter 3 : Sup and Inf

## Level 13

This proof will be easy now.
-/

def bdd (X : set ℝ) := bdd_above X ∧ bdd_below X
def complete (X : set ℝ) := ∀ Y : set ℝ, Y.nonempty ∧ Y ⊆ X ∧ bdd Y → ∃ s i : ℝ, is_lub Y s ∧ is_glb Y i 


/- Lemma
The rational numbers are not complete.

Need to complete the proof.
-/
lemma not_complete_rationals : 
    ¬ complete embedded_rationals :=
begin
   sorry,
end

end xena -- hide
