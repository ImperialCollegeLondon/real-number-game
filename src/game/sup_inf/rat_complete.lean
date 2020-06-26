import game.sup_inf.unbdd_iff
import data.real.basic

namespace xena -- hide

/-
# Chapter 3 : Sup and Inf

## Level 13

This proof will be easy now.
Actually this needs quite some work due to coercions etc.
May need to change definitions.
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
   -- the plan here is to use the set { x : ℚ | x ^2 < 2}
   -- this is bounded, and the sup S will satisfy neither
   -- S ^ 2 < 2 nor S ^ 2 > 2 (due to density of rationals)
   -- so S ^ 2 = 2, but there's not such S ∈ ℚ
   -- (as per sets/sqrt2NotRational.lean)
   intro H,
   set Y : set ℝ := { y | ∃ x : ℚ, y = ↑x ∧  x ^ 2 < (2:ℚ) } with hY,
   -- Y is not empty
   have h1Y : Y.nonempty, sorry,
   have h2Y : Y ⊆ embedded_rationals, sorry,
   have h3Y : bdd Y, sorry,
   have G := H Y (and.intro h1Y (and.intro h2Y h3Y)), 
   cases G with S hsi, cases hsi with I hsi, cases hsi with hS hI,
   cases lt_trichotomy (S ^ 2) 2 with hSn hS2,
   {   -- case S ^ 2 < 2 can be sorted out: rationals are dense
       sorry, 
    },
   cases hS2 with hS hSp, swap,
   { -- case 2 < S^2 can also be sorted out using density of rationals
       sorry,
   },
   { -- the interesting case S^2 = 2, trouble because of coercions, S is real!!
        sorry,
   },

end

end xena -- hide
