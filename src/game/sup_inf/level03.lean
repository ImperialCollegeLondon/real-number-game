import data.real.basic

definition is_upper_bound (S : set ℝ) (x : ℝ) := ∀ s ∈ S, s ≤ x 
definition is_lub' (S : set ℝ) (x : ℝ) := is_upper_bound S x ∧ 
  ∀ y : ℝ, is_upper_bound S y → x ≤ y
definition has_lub (S : set ℝ) := ∃ x, is_lub' S x 

/- 
The next result must be placed in the sidebar axioms.
-/

-- part (c) (i)
definition reals_lt_59 := {x : ℝ | x < 59}

theorem helper_lemma (x y : ℝ) (H : x < y) : x < (x + y) / 2 ∧ (x + y) / 2 < y :=
begin
  have two_ge_zero : (2 : ℝ) ≥ 0 := by norm_num,
  split,
  { apply lt_of_mul_lt_mul_right _ two_ge_zero,
    rw [mul_two,div_mul_cancel],
    apply add_lt_add_left H,
    norm_num},
  { apply lt_of_mul_lt_mul_right _ two_ge_zero,
    rw [div_mul_cancel,mul_two],
    apply add_lt_add_right H,
    norm_num,
  },
end

/- Lemma
The LUB of...
-/
lemma lub_of_open_set : is_lub' reals_lt_59 59 := 
begin
  split,
  { intros s Hs,
    exact le_of_lt Hs,
  },
  { intros y Hy,
    apply le_of_not_gt,
    intro H,
    let s := (y + 59) / 2,
    have H1 : y < s := (helper_lemma _ _ H).1,
    have H2 : s < 59 := (helper_lemma _ _ H).2,
--    unfold is_upper_bound at Hy,
    have H1' := Hy s H2,
    exact not_le_of_lt H1 H1', --of_not_gt
  }
end 
