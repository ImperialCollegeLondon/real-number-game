import data.real.basic

definition is_upper_bound (S : set ℝ) (x : ℝ) := ∀ s ∈ S, s ≤ x 
definition is_lub' (S : set ℝ) (x : ℝ) := is_upper_bound S x ∧ 
  ∀ y : ℝ, is_upper_bound S y → x ≤ y
definition has_lub (S : set ℝ) := ∃ x, is_lub' S x 

/- Lemma
Any non-empty and bounded set of reals has a supremum.
-/
theorem nonempty_and_bounded_of_has_LUB (S : set ℝ) (H : has_lub S) : 
  (S ≠ ∅) ∧ (∃ x, is_upper_bound S x) :=
begin
  cases H with b Hb,
  -- b is LUB, Hb is proof it's LUB
  split,
  { intro Hempty,
    -- b is LUB of S, and S is empty.
    -- seek contradiction.
    have H := Hb.2 (b - 1), -- b - 1 is an upper bound
    have Hub : is_upper_bound S (b - 1),
    { intros s Hs,
      exfalso,
      rw Hempty at Hs,
      exact Hs,
    },
      have Hwrong := H Hub,
      linarith,
  }  ,
  {
     existsi b,
     exact Hb.1
  }
end 

