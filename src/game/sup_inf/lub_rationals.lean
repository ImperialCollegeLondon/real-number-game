import data.real.basic

namespace xena -- hide

/-
# Chapter 3 : Sup and Inf

## Level 11
-/


definition is_upper_bound (S : set ℝ) (x : ℝ) := ∀ s ∈ S, s ≤ x 
definition is_lub' (S : set ℝ) (x : ℝ) := is_upper_bound S x ∧ 
  ∀ y : ℝ, is_upper_bound S y → x ≤ y
definition has_lub (S : set ℝ) := ∃ x, is_lub' S x 

def embedded_rationals : set ℝ := {x : ℝ | ∃ y : ℚ, x = ↑y}

/- Lemma
The set of rational numbers does not have a supremum
-/
lemma not_lub_rationals : ∀ b : ℝ, ¬ (is_lub (embedded_rationals) b) :=
begin
intros b Hlub,
have Hbub : b ∈ upper_bounds embedded_rationals := Hlub.left,
have H : b < (b+1) := calc b = b+0 : (add_zero _).symm
                         ... < b+1 : add_lt_add_left zero_lt_one _,
cases (exists_rat_btwn H) with q Hq,
have Hqin : ↑q ∈ embedded_rationals := ⟨q,rfl⟩,
have Hwrong2 := Hbub Hqin,
exact not_lt.2 Hwrong2 (Hq.left),
end

end xena -- hide
