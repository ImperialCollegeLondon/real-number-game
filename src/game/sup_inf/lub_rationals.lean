import data.real.basic

definition is_upper_bound (S : set ℝ) (x : ℝ) := ∀ s ∈ S, s ≤ x 
definition is_lub' (S : set ℝ) (x : ℝ) := is_upper_bound S x ∧ 
  ∀ y : ℝ, is_upper_bound S y → x ≤ y
definition has_lub (S : set ℝ) := ∃ x, is_lub' S x 

def S3b : set ℝ := {x : ℝ | ∃ y : ℚ, x = ↑y}

/- Lemma
Rationals have no sup...
-/
theorem Q3b : ∀ b : ℝ, ¬ (is_lub (S3b) b) :=
begin
intros b Hlub,
have Hbub : b ∈ upper_bounds S3b := Hlub.left,
have H : b < (b+1) := calc b = b+0 : (add_zero _).symm
                         ... < b+1 : add_lt_add_left zero_lt_one _,
cases (exists_rat_btwn H) with q Hq,
have Hqin : ↑q ∈ S3b := ⟨q,rfl⟩,
have Hwrong2 := Hbub Hqin,
exact not_lt.2 Hwrong2 (Hq.left),
end
