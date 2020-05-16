import tactic.ring
import tactic.linarith
import data.rat.basic
import data.rat.cast

/- Section
1.4 An Application
-/

/- 
Prove that there is no rational number whose square is 2 
using the techniques introduced earlier.
-/

def even (a : ℤ) := ∃ b : ℤ, a = 2 * b
def odd (a : ℤ) := ∃ b : ℤ, a = 2 * b + 1

lemma not_even_is_odd (n : ℤ) : ¬ even n ↔ odd n := 
begin
    split,
    intro ha,
    have hb : n % 2 = 1,
        have hc : n % 2 = 0 ∨ n % 2 = 1,
            apply int.mod_two_eq_zero_or_one,
        cases hc with hx hy,
        exfalso,
        apply ha,
        existsi n / 2,
        rw int.mul_div_cancel_of_mod_eq_zero hx,
        assumption,
    have hc : (n - 1) % 2 = 0,
    have hd : n % 2 = 1 % 2, rw hb, refl,
        revert hd,
        rw int.mod_eq_mod_iff_mod_sub_eq_zero,
        intro h, assumption,
    existsi (n - 1) / 2,
    rw int.mul_div_cancel_of_mod_eq_zero hc,
    simp,

    intro ha,
    intro hb,
    cases ha with x hx,
    cases hb with y hy,
    have hc : n % 2 = 1,
        rw hx, 
        rw [add_comm, int.add_mul_mod_self_left],
        refl,
    have hd : n % 2 = 0,
        rw hy, simp,
    have he : (1 : ℤ) = (0 : ℤ),
        rwa [←hc, ←hd],
    have hf : ¬ ( (1 : ℤ) = (0 : ℤ)), simp,
    exact hf he,
end

lemma gcdeven (n m : ℕ) : 2 ∣ nat.gcd (2 * n) (2 * m) :=
begin
    have ha : 2 ∣ 2 * n, existsi n, refl,
    have hb : 2 ∣ 2 * m, existsi m, refl,
    have hc : (2 ∣ 2 * n) → (2 ∣ 2 * m) → 2 ∣ nat.gcd (2 * n) (2 * m),
    exact nat.dvd_gcd,
    apply hc,
    repeat {assumption},
end
#check gcdeven

/- Lemma
If $a$ is an integer, then $a$ is even if and only if $a^2$ is even.
-/
lemma times_even
  (a : ℤ) : even a ↔ even (a ^ 2) :=
begin
    split,
    intro h,
    have ha : ∃ b : ℤ, a = 2 * b, exact h,
    have hb : ∃ b : ℤ, a ^ 2 = 2 * b,
        cases ha with x hx,
        existsi 2 * x ^ 2,
        rw hx,
        ring,
    exact hb,

    intro h,
    apply classical.by_contradiction,
    intro ha,
    have hc : odd a,
        rw ←not_even_is_odd a,
        assumption,
    have hd : odd (a ^ 2),
        cases hc with x hx,
        existsi 2 * x ^ 2 + 2 * x,
        rw hx,
        ring,
    have he : ¬ even (a ^ 2),
        rw not_even_is_odd (a ^ 2),
        assumption,
    exact he h,
end

/- Theorem
There is no rational number whose square is 2.
-/
theorem rational_not_sqrt_two : ¬ ∃ r : ℚ, r ^ 2 = 2  := 
begin
    -- First show that p is even
    push_neg,
    intro r,
    -- Manipulate the fraction to have the properties desired
    have h : rat.mk (r.num) (r.denom) = r,
        apply rat.num_denom,
    rw ←h,
    intro hcon,
    -- The denominator must not be zero
    have hdnot0 : r.denom ≠ 0,
        intro ha,
        have hb : rat.mk (r.num) (r.denom) ^ 2 = 0,
            rw ha,
            refl,
        convert hb,
        rw hcon,
        simp,
        linarith,
    -- The numerator must also not be zero
    have hnnot0 : r.num ≠ 0,
        intro ha,
            have hb : rat.mk (r.num) (r.denom) ^ 2 = 0,
                rw ha,
                simp, refl,
            convert hb,
            rw hcon,
            simp,
            linarith,
    -- The fraction is in its lowest terms
    have hcop : nat.coprime (int.nat_abs r.num) r.denom,
        cases r with ha hb hc hd,
        exact hd,
    -- Now we can begin the actual proof...
    -- First show that r.num ^ 2 is even
    have hsqrneven : even (r.num ^ 2),
        existsi (r.denom : ℤ) ^ 2,
        have ha : r.num ^ 2 = r.num ^ 2 * 1,
            simp,
        rwa [ha, ←rat.mk_eq],
        convert hcon,
        repeat {rw pow_two},
        rw rat.mul_def,
        all_goals {try {simp, apply hdnot0,}},
        simp,
    -- Now we can use times_even to show r.num is even
    have hneven : even r.num, rw times_even, assumption,
    -- r.num is even → r.denom ^ 2 is also even
    have hsqrdeven : even (r.denom ^ 2),
        cases hneven with b ha,
        existsi b ^ 2,
        have hb : (2 * ↑(r.denom) ^ 2 = 4 * (b ^ 2)) → (↑(r.denom) ^ 2 = 2 * b ^ 2),
            have hβ : 4 * b ^ 2 = 2 * 2 * b ^ 2, refl,
            rw [hβ, ←sub_eq_zero],
            have hγ : 2 * ↑(r.denom) ^ 2 - 2 * 2 * b ^ 2 = 2 * (↑(r.denom) ^ 2 - 2 * b ^ 2), ring,
            rw [hγ, mul_eq_zero],
            intro hδ,
            cases hδ with hδ1 hδ2,
            exfalso,
            convert hδ1, simp, linarith,
            rw ←sub_eq_zero,
            assumption,
        rw hb,
        have hc : 4 * b ^ 2 = (2 * b) ^ 2,
            ring,
        rw [hc, ←ha],
    have hd : ↑r.denom * ↑r.denom = r.denom * r.denom, simp,
        have he : rat.mk (r.num ^ 2) (r.denom ^ 2) = 2, 
            rw ←hcon, 
            repeat {rw pow_two}, 
            rw rat.mul_def,
            repeat {simp, apply hdnot0,},
        have hf : rat.mk r.num r.denom = r.num / r.denom, 
            exact rat.mk_eq_div (r.num) ↑(r.denom),
        have hg : 2 * (↑(r.denom) ^ 2) =  r.num ^ 2 * 1 → 2 * (↑(r.denom) * ↑(r.denom)) = r.num * r.num,
            repeat {rw pow_two},
            rw mul_one,
            intro hh,
            assumption,
        rw hg,
        rw ←rat.mk_eq,
        rw he,
        refl,
        simp,
        rw pow_two,
        intro hh,
        have hi : r.denom = 0,
            have hj : r.denom * r.denom = 0,
                rw ←hd,
                exact_mod_cast hh,
            rw nat.mul_eq_zero at hj,
            revert hj,
            simp,
        exfalso,
        exact hdnot0 hi,
    have hdeven : even r.denom, rw times_even, assumption,
    -- But that means r.num and r.denom are not coprimes
    have hncop : ¬ nat.coprime (int.nat_abs (r.num)) (r.denom),
        have ha : ¬ nat.coprime (int.nat_abs (r.num)) (r.denom) ↔ nat.gcd (int.nat_abs (r.num)) (r.denom) ≠ 1, refl,
        rw ha,
        cases hneven with k hk,
        cases hdeven with m hm,
        rw hk,
        have hb : int.nat_abs r.denom = 2 * (int.nat_abs m),
            rwa [hm, int.nat_abs_mul],
            refl,
        have hc : (r.denom : ℕ) = int.nat_abs r.denom, refl,
        rwa [hc, hb],
        have hd : int.nat_abs (2 * k) = 2 * int.nat_abs k, rw int.nat_abs_mul, refl,
        rw hd,
        intro he,
        have hf : ¬ (2 ∣ nat.gcd (2 * int.nat_abs k) (2 * int.nat_abs m)),
            rw he,
            simp,
            linarith,
        have hg : 2 ∣ nat.gcd (2 * int.nat_abs k) (2 * int.nat_abs m),
            apply gcdeven,
        exact hf hg,
    exact hncop hcop,
end