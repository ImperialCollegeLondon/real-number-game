import data.real.basic

/-
# Chapter 1 : Sets

## Level 9
-/

/- 
This is a little more complicated example asking you to work with intervals of reals.
The result will be of help in the sup-inf world.
-/

notation `[` a `,` b `]`  := set.Icc a b

def mem_prod_sets (A : set ℝ) (B : set ℝ) := { x : ℝ | ∃ y ∈ A, ∃ z ∈ B, x = y * z}


/- Lemma
Prove that if $x = 0$, then `x ∈ mem_prod_sets [(-2:ℝ),-1] [(0:ℝ), 3]`
-/
lemma zero_in_prod : (0:ℝ) ∈ mem_prod_sets [(-2:ℝ), -1] [(0:ℝ), 3] :=
begin
  set a0 := (0:ℝ) with ha,
  have h1 : a0 ∈ (set.Icc (0:ℝ) 3), simp, linarith,
  set b := (-2:ℝ) with hb,
  have h2 : b ∈ set.Icc (-2:ℝ) (-1:ℝ), simp, linarith,
  use b, split, exact h2,
  use a0, split, exact h1, rw ha, norm_num, done
end


