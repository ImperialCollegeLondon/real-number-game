import game.sets.L01defs
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

Lean's natural numbers start at zero, so it is convenient to let our sequences start from the zeroth term. In other words, a sequence of reals will be $a_0$...

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

end xena
