import game.max.level03 -- hide

open_locale classical -- hide

noncomputable theory -- hide

namespace xena -- hide

/-
# Chapter 1 : Max

## Level 4

`le_max_right` is the statement that `b ≤ max a b`. There's a short
proof using what we've already done.
-/

/- Hint : 
Why not start with `rw max_comm`?
-/

/- Lemma
For any real numbers $a$ and $b$, we have $b\leq\max(a,b).$
-/

theorem le_max_right (a b : ℝ) : b ≤ max a b :=
begin
  rw max_comm,
  apply le_max_left


end

end xena --hide
