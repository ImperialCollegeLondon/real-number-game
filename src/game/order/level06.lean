import data.real.basic
open real

namespace xena -- hide

/-
# Chapter 2 : Order

## Level 6

An interesting result to prove.
-/



/- Lemma
For any two non-negative real numbers $a$ and $b$, we have that
$$a \le b \iff a^2 \le b^2 $$.
-/
theorem le_iff_sq_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b): a ≤ b ↔ a^2 ≤ b^2:=
begin
    split,
    intro h,
    have h1 : a^2 ≤ a * b, 
        have h11 : a ≤ a, linarith,
        have h12 := mul_le_mul h11 h ha ha,
        have h13 : a * a = a^2, ring,
        rw h13 at h12, exact h12,
    have h2 : a * b ≤ b^2, 
        have h21 : b ≤ b, linarith,
        have h22 := mul_le_mul h21 h ha hb,
        rw mul_comm at h22,
        have h23 : b * b = b^2, ring,
        rw h23 at h22, exact h22,
    exact le_trans h1 h2,
    intro h,
    have ha2 : 0 ≤ a^2, exact pow_nonneg ha 2,
    have hb2 : 0 ≤ b^2, exact pow_nonneg hb 2,
    have h1 := (sqrt_le ha2 hb2).mpr h,
    have h2a := sqrt_sqr ha, 
    have h2b := sqrt_sqr hb,
    rw h2a at h1, rw h2b at h1, exact h1, done

end

end xena -- hide