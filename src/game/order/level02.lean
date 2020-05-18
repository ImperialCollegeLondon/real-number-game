import data.real.basic

namespace xena -- hide

/-
# Chapter 2 : Order

## Level 2

This level invites you to work out a property of the absolute value.
In Lean the absolute value of $x$ is denoted by `abs x`. 
-/

/- Hint : The definition of the absolute value in mathlib:
definition abs {α : Type u} [decidable_linear_ordered_add_comm_group α] (a : α) : α := max a (-a)
-/

/-
For ease of use, a notation can be wrapped around that definition as below.
-/

notation `|` x `|` := abs x

/- Lemma
For any two real numbers $a$ and $b$, we have that
$$|ab| = |a||b|$$.
-/
theorem abs_prod (a b : ℝ) : |a * b| = |a| * |b| :=
begin
    sorry,
end

end xena --hide
