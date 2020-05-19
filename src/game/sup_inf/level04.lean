import data.real.basic

namespace xena -- hide

/-
# Chapter 3 : Sup and Inf

## Level 4 
-/


definition is_upper_bound (S : set ℝ) (x : ℝ) := ∀ s ∈ S, s ≤ x 
definition is_lub' (S : set ℝ) (x : ℝ) := is_upper_bound S x ∧ 
  ∀ y : ℝ, is_upper_bound S y → x ≤ y
definition has_lub (S : set ℝ) := ∃ x, is_lub' S x 

/-
A generalization of the result in the previous level.
-/

-- begin hide
-- these three helper results to go in sidebar
lemma two_real_ne_zero : (2:ℝ) ≠ 0 :=
begin
    intro, linarith,
end

lemma avg_lt_max {mn mx: ℝ} (H : mn < mx) : (mn+mx) / 2 < mx :=
begin
  apply (mul_lt_mul_right (show (0:ℝ)<2, by norm_num)).1,
  rw [div_mul_cancel _ (two_real_ne_zero)],
  simp [H,mul_two],
end

lemma min_lt_avg {mn mx: ℝ} (H : mn < mx) : mn < (mn+mx) / 2 :=
begin
  apply (mul_lt_mul_right (show (0:ℝ)<2, by norm_num)).1,
  rw [div_mul_cancel _ (two_real_ne_zero)],
  simp [H,mul_two],
end
-- end hide

/- Lemma
A more general version of the previous level...
-/
lemma lub_open (y : ℝ) : is_lub' {x : ℝ | x < y} y :=
begin
split,
{ intros a ha,
  exact le_of_lt ha, 
},
--unfold lower_bounds,
intro b,
intro Hb,
refine le_of_not_gt _,
intro Hnb,
let c:=(b+y)/2,
--unfold upper_bounds at Hb,
have H2 := Hb c,
clear Hb,
have H : c ∈ {x : ℝ | x < y},
{ exact avg_lt_max Hnb,
},
have Hcleb := H2 H,
have Hbltc : b < c := min_lt_avg Hnb,
exact not_lt.2 Hcleb Hbltc,
end

end xena -- hide


