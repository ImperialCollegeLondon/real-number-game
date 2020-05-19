import data.real.basic

namespace xena -- hide

/-
# Chapter 3 : Sup and Inf

## Level 7

Another level that showcases the infimum.
-/

def sum_set_const (A : set ℝ) (c : ℝ) := { x : ℝ | ∃ y ∈ A, x = y + c}


/- Lemma
If $A$ is a set of reals, then
$$ \textrm{inf} (c + A) = c + \textrm{inf} (A)$$
-/
lemma inf_sum_set_const (A : set ℝ) (h1A : A.nonempty)
  (h2A : bdd_below A) (a : ℝ) (c : ℝ): 
  (is_glb A a) → is_glb (sum_set_const A c) (c + a) :=
begin
  intro h,
  cases h with hA hB,
  split,
  -- prove that (c+a) is a lower bound
  intros x h0,
  cases h0 with y h1,
  cases h1 with yA h2,
  sorry, sorry, --needs being worked out
end

end xena -- hide
