import game.max.level01 -- hide

open_locale classical -- hide

noncomputable theory -- hide

namespace xena -- hide

/-
# Chapter 1 : Max

## Level 2

`max_comm` is the statement that `max a b = max b a`. See if you can prove it.

Technical note: in contrast to the natural number game, the `rw` used
in the real number game is Lean's more powerful `rw`, which automatically
tries `refl` after a rewrite. So for example, if after a rewrite a goal
becomes `a = a` then that goal will be closed automatically. Watch out
for vanishing goals!
-/

/- Hint : Hint
Again, do a case split with `cases le_total a b`. 
-/

/- Lemma
For any real numbers $a$ and $b$, we have $\max(a,b) = \max(b,a).$
-/
theorem max_comm (a b : ℝ) : max a b = max b a :=
begin
  cases le_total a b with hab hba,
  { rw max_eq_right hab,
    rw max_eq_left hab,
  },
  { rw max_eq_left hba,
    rw max_eq_right hba
  }  



end

end xena --hide
