import game.max.level02 -- hide

open_locale classical -- hide

noncomputable theory -- hide

namespace xena -- hide

/-
# Chapter 1 : Max

## Level 3

`le_max_left` is the statement that `a ≤ max a b`.

Technical note: `refl` will also close the goal `⊢ a ≤ a` because
`≤` is reflexive. Watch out for goals being randomly closed after
a rewrite.
-/

/- Hint : Tip : `rwa`
The `rwa` tactic means "rewrite, and then close the goal because it's an
assumption". It is shorter than `rw` followed by `exact h`
if `h` is an assumption.
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
