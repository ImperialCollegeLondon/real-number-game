import data.real.basic

/-
# Chapter 1 : Sets

## Level 9

As a final test of your ability in working with sets, prove that the set of rational 
numbers is dense in the reals.

There are several new axioms in the left side bar that will help you in this task.
Note that you may need to change the type of some quantities from rationals to reals.
Lean doesn't necessarily consider the rational $2$ to be the same at the real number $2$.
Some of the axioms on the left make working with the casts from rationals to reals easier.
-/


/- Axiom : inv_prod_self : 
∀ n : ℕ, 0 < n → (1/n : ℝ) * (n : ℝ ) = 1 
-/

/- Axiom : inv_prod_other : 
∀ (m : ℤ), ∀ (n : ℕ), 0 < n → (1/n : ℝ) * (m : ℝ) = (m/n : ℝ)
-/

/- Axiom : archimedean_R : ∀ x : ℝ, 0 < x → ∃ n : ℕ, 0 < n ∧ (1/n : ℝ) < x
-/

/- Axiom : has_ceiling : ∀ x : ℝ,  ∃ m : ℤ, ((m-1) : ℝ) ≤ x ∧ x < (m:ℝ)
-/

-- one way to prove ℚ dense in ℝ 
def dense_in_R (A : set ℝ) := ∀ (x y : ℝ), x < y → ∃ a ∈ A, a ∈ set.Ioo x y
def embedded_rationals : set ℝ := { x | ∃ r : ℚ, x = ↑r }

/- Lemma
Rationals are dense in the reals.
-/
theorem rat_dense_in_R : dense_in_R embedded_rationals := 
begin
    intros x y hxy,
    have H := lt_trichotomy x 0,
    cases H with xL xr, swap, cases xr with x0 xR,
    -- case x = 0
    rw x0 at hxy, 
    have G := archimedean_R y hxy,
    cases G with n hn, cases hn with hnL hnR,
    use (1/n), split, existsi (1/n : ℚ), norm_num,
    split, swap, exact hnR, rw x0, norm_num, exact hnL,
    -- case 0 < x
    have H : 0 < y - x, linarith,
    have G := archimedean_R (y-x) H,
    cases G with n hn, cases hn with hnL hnR, 
    have F := has_ceiling (n*x),
    cases F with m hm, cases hm with hmL hmR,
    use (m/n), split, existsi (m/n : ℚ), norm_num,
    have hnL1 : 0 < (n : ℝ), norm_cast, exact hnL, 
    have hnL2 : 0 < (1/n : ℝ), exact one_div_pos_of_pos hnL1,
    split, exact (lt_div_iff' hnL1).mpr hmR,
    have h1 : (m : ℝ) ≤ n*x + 1, linarith,
    have h2 : (m/n : ℝ) ≤ x + (1/n : ℝ), 
        have h21 := (mul_le_mul_left hnL2).mpr h1, 
        rw mul_add (1/n : ℝ) _ _ at h21, rw mul_one at h21,
        rw ← mul_assoc at h21, 
        have h22 := inv_prod_self n hnL,    --cheating here
        rw h22 at h21, rw one_mul at h21,
        have h23 := inv_prod_other m n hnL, --and here
        rw h23 at h21, exact h21,
    have h3 : x + (1/n : ℝ) < x + (y-x), linarith,
    have h4 : x + (y-x) = y, norm_num, rw h4 at h3,
    linarith, 
    -- case x < 0  -- reduces to the above
     have H : 0 < y - x, linarith,
    have G := archimedean_R (y-x) H,
    cases G with n hn, cases hn with hnL hnR, 
    have F := has_ceiling (n*x),
    cases F with m hm, cases hm with hmL hmR,
    use (m/n), split, existsi (m/n : ℚ), norm_num,
    have hnL1 : 0 < (n : ℝ), norm_cast, exact hnL, 
    have hnL2 : 0 < (1/n : ℝ), exact one_div_pos_of_pos hnL1,
    split, exact (lt_div_iff' hnL1).mpr hmR,
    have h1 : (m : ℝ) ≤ n*x + 1, linarith,
    have h1 : (m : ℝ) ≤ n*x + 1, linarith,
    have h2 : (m/n : ℝ) ≤ x + (1/n : ℝ), 
        have h21 := (mul_le_mul_left hnL2).mpr h1, 
        rw mul_add (1/n : ℝ) _ _ at h21, rw mul_one at h21,
        rw ← mul_assoc at h21, 
        have h22 := inv_prod_self n hnL,    --cheating here
        rw h22 at h21, rw one_mul at h21,
        have h23 := inv_prod_other m n hnL, --and here
        rw h23 at h21, exact h21,
    have h3 : x + (1/n : ℝ) < x + (y-x), linarith,
    have h4 : x + (y-x) = y, norm_num, rw h4 at h3,
    linarith, done
end
