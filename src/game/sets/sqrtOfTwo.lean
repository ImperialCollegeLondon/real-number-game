import data.nat.prime
open nat

theorem sqrt_two_irrational_V1 {a b : ℕ} (co : gcd a b = 1) : a^2 ≠ 2 * b^2 :=
assume h : a^2 = 2 * b^2,
have 2 ∣ a^2,
    by simp [h],
have ha : 2 ∣ a,
    from prime.dvd_of_dvd_pow prime_two this,
-- usually after exists.elim the rest of the proof should be inside
-- parantheses
exists.elim ha (assume c : ℕ, assume aeq : a = 2 * c, 
have 2 * (2 * c^2) = 2 * b^2,
    by simp [eq.symm h, aeq]; 
       simp [nat.pow_succ, mul_comm, mul_assoc, mul_left_comm],
have 2 * c^2 = b^2,
    from eq_of_mul_eq_mul_left dec_trivial this,
have 2 ∣ b^2, 
    by simp [eq.symm this],
have hb : 2 ∣ b,
    from prime.dvd_of_dvd_pow prime_two this,
have 2 ∣ gcd a b,
    from dvd_gcd ha hb,
have habs : 2 ∣ (1:ℕ), 
    by simp * at *,
-- therefore the ) below!!!!
show false, from absurd habs dec_trivial )
#check sqrt_two_irrational_V1

-- tactics mode
theorem sqrt_two_irrational_V2 {a b : ℕ} (co : gcd a b = 1) : a^2 ≠ 2 * b^2 :=
begin
    intro h,
    have h1 : 2 ∣ a^2, by simp [h],
    have h2 : 2 ∣ a, from prime.dvd_of_dvd_pow prime_two h1,
    cases h2 with c aeq,
    have h3 : 2 * (2 * c^2) = 2 * b^2,
        by simp [eq.symm h, aeq];
            simp [nat.pow_succ, mul_comm, mul_assoc, mul_left_comm],
    have h4 : 2 * c^2 = b^2,
        from eq_of_mul_eq_mul_left dec_trivial h3,
    have h5 : 2 ∣ b^2,
        by simp [eq.symm h4],
    have hb : 2 ∣ b,
        from prime.dvd_of_dvd_pow prime_two h5,
    have h6 : 2 ∣ gcd a b, from dvd_gcd (exists.intro c aeq) hb,
    have habs : 2 ∣ (1:ℕ), by simp * at *,
    exact absurd habs dec_trivial, done
end

-- using let (it may introduce a bug due to _let_match hypothesis)
theorem sqrt_two_irrational_V3 {a b : ℕ} (co : gcd a b = 1) : a^2 ≠ 2 * b^2 :=
assume h : a^2 = 2 * b^2,
have 2 ∣ a^2,
    by simp [h],
have ha : 2 ∣ a,
    from prime.dvd_of_dvd_pow prime_two this, 
let ⟨c, aeq⟩ := ha in
have 2 * (2 * c^2) = 2 * b^2,
    by simp [eq.symm h, aeq]; 
       simp [nat.pow_succ, mul_comm, mul_assoc, mul_left_comm],
have 2 * c^2 = b^2,
    from eq_of_mul_eq_mul_left dec_trivial this,
have 2 ∣ b^2, 
    by simp [eq.symm this],
have hb : 2 ∣ b,
    from prime.dvd_of_dvd_pow prime_two this,
have 2 ∣ gcd a b,
    from dvd_gcd ha hb,
have habs : 2 ∣ (1:ℕ), 
    by clear_aux_decl; simp * at *, -- replaces simp * at *,
show false, from absurd habs dec_trivial 

-- variant with match, needs end to finish
theorem sqrt_two_irrational_V4 {a b : ℕ} (co : gcd a b = 1) : a^2 ≠ 2 * b^2 :=
assume h : a^2 = 2 * b^2,
have 2 ∣ a^2,
    by simp [h],
have ha : 2 ∣ a,
    from prime.dvd_of_dvd_pow prime_two this,
match ha with | ⟨c, aeq⟩ :=
have 2 * (2 * c^2) = 2 * b^2,
    by simp [eq.symm h, aeq]; 
       simp [nat.pow_succ, mul_comm, mul_assoc, mul_left_comm],
have 2 * c^2 = b^2,
    from eq_of_mul_eq_mul_left dec_trivial this,
have 2 ∣ b^2, 
    by simp [eq.symm this],
have hb : 2 ∣ b,
    from prime.dvd_of_dvd_pow prime_two this,
have 2 ∣ gcd a b,
    from dvd_gcd ha hb,
have habs : 2 ∣ (1:ℕ), 
    by clear_aux_decl; simp * at *, -- replaces simp * at *,
show false, from absurd habs dec_trivial 
end

theorem sqrt_two_irrational {a b : ℕ} (co : gcd a b = 1) :
  a^2 ≠ 2 * b^2 :=
assume h : a^2 = 2 * b^2,
have 2 ∣ a^2,
  by simp [h],
have 2 ∣ a,
  from prime.dvd_of_dvd_pow prime_two this,
exists.elim this $
assume (c : nat) (aeq : a = 2 * c),
have 2 * (2 * c^2) = 2 * b^2,
  by simp [eq.symm h, aeq];
    simp [nat.pow_succ, mul_comm, mul_assoc, mul_left_comm],
have 2 * c^2 = b^2,
  from eq_of_mul_eq_mul_left dec_trivial this,
have 2 ∣ b^2,
  by simp [eq.symm this],
have 2 ∣ b,
  from prime.dvd_of_dvd_pow prime_two this,
have 2 ∣ gcd a b,
  from dvd_gcd ‹2 ∣ a› ‹2 ∣ b›,
have 2 ∣ (1 : ℕ),
  by simp * at *,
show false, from absurd ‹2 ∣ 1› dec_trivial
#check sqrt_two_irrational
