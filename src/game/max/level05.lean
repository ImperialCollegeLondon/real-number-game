import game.max_and_abs.level04 -- hide

open_locale classical -- hide

noncomputable theory -- hide

namespace xena -- hide

/-
# Chapter ? : Max and abs

## Level 5

`max_le` is really useful; it says that if `a ≤ c` and `b ≤ c`
then `max a b ≤ c`.

Note that in the Lean formulation, the variables are *implicit*,
meaning that Lean will guess them.
-/

/- Lemma
If $a$, $b$, $c$ are real numbers with $a\leq c$ and $b\leq c$,
then $\max(a,b)\leq c.$
-/
theorem max_le {a b c : ℝ} (hac : a ≤ c) (hbc : b ≤ c) : max a b ≤ c :=
begin
  cases max_choice a b with ha hb,
  { rw ha,
    assumption
  },
  { rw hb,
    assumption
  }


end

end xena --hide
