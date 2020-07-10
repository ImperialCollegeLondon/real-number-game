import game.max.level02 -- hide

open_locale classical -- hide

noncomputable theory -- hide

namespace xena -- hide

/-
# Chapter ? : Max and abs

## Level 3

`le_max_left` is the statement that `a ≤ max a b`.

Technical note: in contrast to the natural number game, the `rw` used
in the real number game is Lean's more powerful `rw`, which automatically
tries `refl` after a rewrite; note that `≤` is reflexive, so `refl` will
close a goal of the form `a ≤ a`. 
-/

/- Lemma
For any real numbers $a$ and $b$, we have $a\leq\max(a,b).$
-/
theorem le_max_left (a b : ℝ) : a ≤ max a b :=
begin
  cases le_total a b with hab hba,
  { rw max_eq_right hab,
    assumption
  },
  { rw max_eq_left hba,
    -- Lean closes a ≤ a automatically because ≤ is reflexive
  }  


end

end xena --hide
