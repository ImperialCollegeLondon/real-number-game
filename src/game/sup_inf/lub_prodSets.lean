import ..sup_inf.supProdConst
import ..sets.sets_level09

namespace xena -- hide

/-
# Chapter 3 : Sup and Inf

## Level 9

An intermediary result to be used in the next level.
-/

-- main result in lemma sup_mem_prod_of_sets
-- begin hide
--def mem_prod_sets (A : set ℝ) (B : set ℝ) := { x : ℝ | ∃ y ∈ A, ∃ z ∈ B, x = y * z}
-- end hide


/-
Prove that a given real number is the supremum of a particular set.
-/

/- Lemma
Given two sets of reals $A$ and $B$, show that given real number is the LUB
of their elementwise product `mem_prod_sets`.
-/
lemma mem_prod_sets_lub_proof : 
  is_lub (mem_prod_sets (set.Icc (-2:ℝ) (-1:ℝ)) (set.Icc (0:ℝ) (3:ℝ)) ) 0 := 
begin
  split,
  intros x h1,
  cases h1 with a hh, cases hh with ha h2,
  cases h2 with b h3, cases h3 with hb hx,
  have H : a ≤ 0, 
    cases ha with hg hl,
    linarith,
  have G : b ≥ 0, 
    cases hb with hg hl, exact hg,
  rw hx, exact mul_nonpos_of_nonpos_of_nonneg H G,
  intros x hx,
  by_contradiction hnx,
  push_neg at hnx,
  --TODO: kmb doesn't know what zero_in_prod is, and it's not compiling
  have E := zero_in_prod,
  have D := hx 0 E, linarith, done
  --sorry
end

end xena -- hide

