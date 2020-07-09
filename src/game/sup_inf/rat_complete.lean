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
def complete (X : set ℝ) := 
    ∀ Y : set ℝ, Y.nonempty ∧ Y ⊆ X ∧ bdd Y → ∃ s ∈ X, is_lub Y s ∧ ∃ i ∈ X, is_glb Y i


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
   set Y : set ℝ := { y | ∃ x : ℚ, y = ↑x ∧ 0 ≤ x ∧ x ^ 2 < (2:ℚ) } with hY,
   -- Y is not empty
   have h1Y : Y.nonempty, 
   {  --change ∃ y : ℝ, y ∈ Y,
      use (0: ℝ), use (0 : ℚ), split, norm_cast, split,
      linarith, rw [pow_two, zero_mul], linarith,
   },
   have h2Y : Y ⊆ embedded_rationals, 
   {  intros y hy, --unfold embedded_rationals,
      cases hy with x hy1, cases hy1 with hyx hy2, --simp,
      use x, exact hyx,
    },
   have h3Y : bdd Y, 
   { split, 
     -- bdd_above
     use (2:ℝ), intros y hy, 
     cases hy with x hx1, cases hx1 with hxy hx2, cases hx2 with hx3 hx4,
     have h1 : (2 : ℝ) < 4, linarith, 
     have h2 : (x ^ 2 : ℝ) < 4, norm_cast, linarith,
     have h3 : 0 ≤ (x ^ 2 : ℝ), exact pow_two_nonneg x,
     have h4 : 0 ≤ (4:ℝ), linarith, 
     have h5 := (real.sqrt_lt h3 h4).mpr h2,
     have h51 : 0 ≤ (x : ℝ), norm_cast, exact hx3,
     have h6 := real.sqrt_sqr h51, rw h6 at h5, rw ← hxy at h5,
     have h7 : (4 : ℝ) = 2 ^ 2, norm_num, rw h7 at h5,
     have h71 : 0 ≤ (2 : ℝ), linarith,
     have h8 := real.sqrt_sqr h71, rw h8 at h5, linarith,
     -- bdd_below
     use (0:ℝ), intros y hy,
     cases hy with x hx1, cases hx1 with hxy hx2, cases hx2 with hx3 hx4,
     rw hxy, norm_cast, exact hx3,
   },
   have G := H Y (and.intro h1Y (and.intro h2Y h3Y)), 
   cases G with S hsi, cases hsi with I hsi, cases hsi with hS hI,
   cases lt_trichotomy (S ^ 2) 2 with hSn hS2,
   {   -- case S ^ 2 < 2 can be sorted out: use Archimedean property / density
       sorry, 
    },
   cases hS2 with hS hSp, swap,
   { -- case 2 < S^2 can also be sorted out using density of rationals
       sorry,
   },
   { -- the interesting case S^2 = 2, maybe some trouble because of coercions?
        sorry,
   },

end

end xena -- hide
