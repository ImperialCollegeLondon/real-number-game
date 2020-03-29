import data.real.basic

axiom well_ordered_Zplus 
  (A : set ℤ) (h1A : A.nonempty) (h2A : ∀ (a:ℤ), a ∈ A → 0 < a): 
  ∃ m ∈ A, ∀ k ∈ A, m ≤ k 
-- this does work!
lemma wellOrd_ceil_existence (x : ℝ) (hx : 0 < x) : 
  ∃ m : ℤ, m > 0 ∧ (m-1 : ℝ) ≤ x ∧ x < (m : ℝ) :=
begin
  have H := exists_nat_gt x,
  cases H with n hn,
  have h1 : 0 < (n : ℝ), exact lt_trans hx hn,
  set A := { k : ℤ | x < k } with hA,
  have h2a : ∀ (a : ℤ), a ∈ A → 0 < a,
    intros a ha,
    have h2a1 : x < a, exact ha,
    have h2a2 : 0 < (a:ℝ), exact lt_trans hx h2a1,
    exact int.cast_lt.mp h2a2,
  have h2 : (n : ℤ) ∈ A, exact hn, 
  have h3 : A.nonempty, existsi (n : ℤ), exact h2,
  have h4 := well_ordered_Zplus A h3 h2a,
  cases h4 with m hmn,
  cases hmn with hm hk,
  have h5 : x < m, exact hm,
  set m1 := m-1 with hm1,
  have h6 : (m1 : ℝ) ≤ x, 
    by_contradiction hf,
    push_neg at hf,
    have h6a : m1 ∈ A, exact hf,
    have h6b := hk m1 h6a, rw hm1 at h6b, linarith,
  existsi m,
  split, swap, split, swap, exact h5, swap,
  have h7 : 0 < (m : ℝ), exact lt_trans hx h5, 
  exact int.cast_lt.mp h7,
  rw hm1 at h6, convert h6, norm_cast, done 
end
-- how to deal with the lambda (uniqueness part)?
-- needs more work
lemma wellOrd_ceil_existuniq (x : ℝ) (hx : 0 < x) : 
  ∃! m : ℕ, m > 0 ∧ (m-1 : ℝ) ≤ x ∧ x < (m : ℝ) :=
begin
  split, 
  split,
  sorry, sorry,
end
