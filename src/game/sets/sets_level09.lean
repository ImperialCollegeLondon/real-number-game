import kb_real_defs

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
If $x = 0$, then `x ∈ mem_prod_sets [(-2:ℝ),-1] [(0:ℝ), 3]`
-/
lemma zero_in_prod : (0:ℝ) ∈ mem_prod_sets [(-2:ℝ), -1] [(0:ℝ), 3] :=
begin
  rw mem_prod_sets,
  dsimp,
  use -2,
  split, 
  { rw mem_Icc_iff,
    split; linarith
  },
  use 0,
  split,
  { rw mem_Icc_iff,
    split; linarith
  },
  norm_num
end


