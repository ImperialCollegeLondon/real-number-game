import game.sup_inf.L01defs
import tactic.linarith

namespace xena -- hide
notation `|` x `|` := abs x -- hide

lemma zero_of_abs_lt_all (x : ℝ) (h : ∀ ε > 0, |x| < ε) : x = 0 :=
eq_zero_of_abs_eq_zero $ eq_of_le_of_forall_le_of_dense (abs_nonneg x) $ λ ε ε_pos, le_of_lt (h ε ε_pos)

-- The next few things should be hidden
@[user_attribute]
meta def ineq_rules : user_attribute :=
{ name := `ineq_rules,
  descr := "lemmas usable to prove inequalities" }

attribute [ineq_rules] add_lt_add le_max_left le_max_right

meta def inequality := `[linarith <|> apply_rules ineq_rules]
run_cmd add_interactive [`inequality]
-- end of scary things


-- World name : Sequences and limits

/-
# Chapter 2 : Sequences and limits

# Level 1 : Introduction to sequences.

Lean's natural numbers start at zero, so it is convenient to let our sequences start from the zeroth term.
In other words, a sequence of reals will be $a₀, a₁, a₂,\ldots$. Let's just step back a minute and think
about what a sequence *is*. If $n$ is a natural number then $a_n$ is a real number, so $n\mapsto a_n$ is actually
a function from natural numbers to real numbers. If we just call this function $a$ then the $n$th term in the sequence
will be called `a(n)` or `a n` rather than $a_n$ but this is OK.

The key definition we want is the concept of a limit of a sequence.
-/
definition is_limit (a : ℕ → ℝ) (l : ℝ) := ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |a n - l| < ε
/-
Let's now prove the basic fact that a sequence has at most one limit. 
-/
/- Lemma
If $a_n \to \ell$ and $a_n \to m$ then $\ell = m$. 
-/
lemma limit.unique (a : ℕ → ℝ) (l m : ℝ) (hl : is_limit a l) (hm : is_limit a m) : l = m :=
begin
  wlog h : l ≤ m,
  rw le_iff_lt_or_eq at h,
  cases h,
    exfalso,
    generalize h : (m - l) / 2 = ε,
    have hε : 0 < ε,
      {inequality},
    cases (hl ε hε) with L hL,
    cases (hm ε hε) with M hM,
    have hL' := hL (max L M) (le_max_left _ _),
    have hM' := hM (max L M) (le_max_right _ _),
    rw abs_lt at hL',
    rw abs_lt at hM',
    cases hL', cases hM',
    linarith,
  assumption,

end

lemma le_zero_abs_pos (c : ℝ) (hle : c < 0) : |c| > 0 :=
begin
  rcases lt_trichotomy c 0 with hc|hc|hc,
  have ne := ne_of_lt hc,
  rw gt_iff_lt,
  rw abs_pos_iff,
  exact ne,
  have ne := ne_of_lt hle,
  exfalso,
  exact ne hc,
  have ne := ne_of_lt hle,
  rw gt_iff_lt,
  rw abs_pos_iff,
  exact ne,
end

lemma abs_pos_eq_pos (b : ℝ) (h_g_0 : b > 0) : abs b = b :=
begin
  rcases lt_trichotomy b 0 with hb|hb|hb,
  exfalso,
  have ne := not_le_of_lt hb,
  rw le_iff_eq_or_lt at ne,
  have r := or.intro_right (0 = b) h_g_0,
  exact ne r,
  exfalso,
  rw gt_iff_lt at h_g_0,
  have f := not_le_of_lt h_g_0,
  rw le_iff_eq_or_lt at f,
  have res := or.intro_left (b < 0) hb,
  exact f res,
  have or_b := (or.intro_right (0 = b) hb),
  rw le_iff_eq_or_lt.symm at or_b,
  rw abs_eq or_b,
  have id : b = b,
  refl,
  have res := or.intro_left (b = -b) id,
  exact res,
end

lemma abs_preserves_mul_le {a b c : ℝ} (hab : |a| < b) (hbg : b > 0) (hnc : c ≠ 0) : |c * a | < |c| * b :=
begin
  rw abs_mul c a,
  have non_neg := (abs_nonneg c),
  rw ge_iff_le at non_neg,
  rw le_iff_eq_or_lt at non_neg,
  cases non_neg,
  rw abs_pos_iff.symm at hnc,
  have f := not_le_of_lt hnc,
  rw le_iff_eq_or_lt at f,
  have res := or.intro_left (abs c < 0) non_neg.symm,
  exfalso,
  exact f res,
  rw mul_lt_mul_left non_neg,
  exact hab,
end

lemma limit.const_mult (a : ℕ → ℝ) (l m c : ℝ) (hl : is_limit a l) : is_limit (λ n, c * (a n)) (l*c) :=
begin
  rcases lt_trichotomy c 0 with hc|hc|hc,
  assume ε : ℝ,
  have ac := le_zero_abs_pos c hc,
  rw gt_iff_lt at ac,
  intro zgε,
  have zge := div_pos zgε ac,
  have zgε' : 0 < ε / |c|,
  apply zge,
  have hle := hl (ε / (abs c)) zgε',
  apply exists.elim hle,
  intros,
  apply exists.intro a_1,
  assume n : ℕ,
  intro,
  simp,
  rw mul_comm,
  rw neg_eq_neg_one_mul,
  have res := a_2 n a_3,
  have assoc : (-1) * (l * c) = ((-1) * l) * c,
  rw mul_assoc,
  rw assoc,
  have dist : a n * c + (-1) * l * c = (a n + (-1) * l) * c,
  rw right_distrib,
  rw dist,
  rw abs_mul,
  simp,
  rw (mul_lt_mul_right ac).symm at res,
  simp at res,
  have rhs_simp : (ε / (abs c)) * |c| = ε,
  have cnez : |c| ≠ 0,
  have hc' := not_le_of_lt ac,
  rw lt_iff_le_and_ne at ac,
  exact ac.2.symm,
  rw div_mul_cancel ε cnez,
  rw rhs_simp at res,
  exact res,
  rw hc,
  rw mul_zero,
  simp,
  assume ε : ℝ,
  intro zgε,
  have hle := hl ε zgε,
  apply exists.elim hle,
  intros,
  apply exists.intro a_1,
  assume n : ℕ,
  intro,
  simp,
  exact zgε,
  assume ε : ℝ,
  have cec := abs_pos_eq_pos c hc,
  have ac : 0 < |c|,
  rw cec,
  exact hc,
  intro zgε,
  have zge := div_pos zgε ac,
  have zgε' : 0 < ε / |c|,
  apply zge,
  have hle := hl (ε / (abs c)) zgε',
  apply exists.elim hle,
  intros,
  apply exists.intro a_1,
  assume n : ℕ,
  intro,
  simp,
  rw mul_comm,
  rw neg_eq_neg_one_mul,
  have res := a_2 n a_3,
  have assoc : (-1) * (l * c) = ((-1) * l) * c,
  rw mul_assoc,
  rw assoc,
  have dist : a n * c + (-1) * l * c = (a n + (-1) * l) * c,
  rw right_distrib,
  rw dist,
  rw abs_mul,
  simp,
  rw (mul_lt_mul_right ac).symm at res,
  simp at res,
  have rhs_simp : (ε / (abs c)) * |c| = ε,
  have cnez : |c| ≠ 0,
  have hc' := not_le_of_lt ac,
  rw lt_iff_le_and_ne at ac,
  exact ac.2.symm,
  rw div_mul_cancel ε cnez,
  rw rhs_simp at res,
  exact res,
end
end xena