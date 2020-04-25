import data.real.basic
open real

/-
# Chapter 2 : Order

## Level 9

This level invites you to work out a property of the absolute value.
In Lean the absolute value of $x$ is denoted by `abs x`. 
For ease of use, a notation can be used around that definition as below.
Feel free to use the triangle inequality on the real numbers,

`abs_add : ∀ (a b : ?M_1), |a + b| ≤ |a| + |b|`

together with the `linarith` and `norm_num` tactics.
-/

notation `|` x `|` := abs x

-- begin hide
-- this to go in the side bar
lemma eq_sqr_to_eq (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : a^2 = b^2 → a = b :=
begin
    intro H,
    have A : sqrt (a ^ 2) = sqrt (a ^ 2), refl,
    rw H at A {occs := occurrences.pos [2]},
    have G := sqrt_sqr ha, rw G at A,
    have F := sqrt_sqr hb, rw F at A, 
    exact A, done
end
-- end hide

/- Lemma
For any two real numbers $a$ and $b$, we have that
$$|a + b| = |a| + |b|$$ if and only if $ab \ge 0$ .
-/
theorem abs_sub_eq_sum_abs (a b : ℝ) : |a + b| = |a| + |b| ↔ a * b ≥ 0 :=
begin
    have H0 : (a+b)^2 = |a+b|^2, 
        have h01 := abs_mul_abs_self (a+b),
        rw pow_two _, rw pow_two _, symmetry, exact h01,
    have H1 : 0 ≤ (a + b) ^ 2, exact pow_two_nonneg (a+b),
    have H2 : (a+b) ^ 2 = a ^2 + 2 * a * b + b^2, ring,
    have H3 : ( |a| + |b| )^2 = |a|^2 + 2*|a|*|b| + |b|^2, ring,
    rw H0 at H2,
    have Ha : a^2 = |a|^2, 
        have h01 := abs_mul_abs_self a,
        rw pow_two _, rw pow_two _, symmetry, exact h01,
    have Hb : b^2 = |b|^2, 
        have h01 := abs_mul_abs_self b,
        rw pow_two _, rw pow_two _, symmetry, exact h01,
    rw [Ha, Hb] at H2,
    split,
    intro h,
    rw h at H2, rw H3 at H2, simp at H2, 
    rw mul_assoc at H2, rw mul_assoc at H2,
    have g1 : ( |a| * |b| ) = (a * b), linarith,
    have g2 : |a * b| = ( |a| * |b| ), exact abs_mul _ _, 
    rw ← g2 at g1,
    by_contradiction hn, push_neg at hn,
    have g3 : | a * b | = - (a *b), exact abs_of_neg hn,
    rw g1 at g3, linarith,
    -- the right-left direction
    intro h,
    have g1 : |a * b| = a * b, exact abs_of_nonneg h,
    have g2 : |a * b| = ( |a| * |b| ), exact abs_mul _ _,
    rw g2 at g1, rw mul_assoc 2 a b at H2,
    rw ← g1 at H2,
    have g3 : |a| ^ 2 + 2 * ( |a| * |b| ) + |b| ^ 2 = ( |a| + |b| )^2, ring,
    rw g3 at H2,
    have g4 : sqrt ( |a + b| ^ 2 ) = sqrt ( |a + b| ^ 2), refl,
    rw H2 at g4 {occs := occurrences.pos [2]},
    have hab : 0 ≤ |a + b|,  exact is_absolute_value.abv_nonneg abs (a+b),
    have ha : 0 ≤ |a|,  exact is_absolute_value.abv_nonneg abs a,
    have hb : 0 ≤ |b|,  exact is_absolute_value.abv_nonneg abs b,
    have hc : 0 ≤ |a| + |b|, linarith,
    have G := eq_sqr_to_eq ( |a + b| ) ( |a| + |b| ) hab hc H2, exact G, done
end


