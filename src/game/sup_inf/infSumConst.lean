import game.sup_inf.infSumSets
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
  { have h2 := hA yA, linarith, },
  -- prove that (c+a) is the GLB
  intros L hL,
  have h3 : L - c ∈ lower_bounds A,
    intros y hy,
    set x := y + c with hx,
    have h31 : x ∈ sum_set_const A c,
      unfold sum_set_const, 
      split, swap, use y, split, exact hy, exact hx,
    have h32 := hL h31, rw hx at h32, linarith,
  have h4 := hB h3, linarith,
  done
end

end xena -- hide
