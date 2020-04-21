import data.real.basic

/-
# Chapter 3 : Sup and Inf

## Level 7

Again a classical result.
-/

-- supremum of constant × set
def const_times_set (c: ℝ) (A : set ℝ) := { x : ℝ | ∃ y ∈ A, x = c * y }

/- Lemma
If $A$ is a set of reals and $c > 0$, then
$$ \textrm{sup} (cA) = c \cdot \textrm{sup} (A)$$
-/
lemma sup_const_times_set (c : ℝ) (hc: 0 < c) (A : set ℝ) (h1A : A.nonempty)
  (h2A : bdd_above A) (a : ℝ) : 
  (is_lub A a) → is_lub (const_times_set c A) (c * a) :=
begin
  intro h,
  cases h with hA1 hA2,
  split,
  { -- prove that (c*a) is an upper bound
    intros x h0,
    cases h0 with y h1, cases h1 with yA h2,
    have H13A := hA1 yA, rw h2, 
    exact (mul_le_mul_left hc).mpr H13A,
  },
  -- now prove that (c*a) is the least upper bound
  intros S hS,
  set y1 := S / c with hys,
  have H : y1 ∈ upper_bounds A,
    intros x hx,
    have G := hA1 hx, 
    set xc := c * x with hxc,
    have G1 : xc ∈ const_times_set c A, 
        use x, existsi hx, exact hxc,
    have G2 := hS G1, rw hxc at G2,  
    rw hys, exact (le_div_iff' hc).mpr G2,
  have F := hA2 H, rw hys at F, 
  have E := (mul_le_mul_left hc).mpr F,
  exact (le_div_iff' hc).mp F, done
end
