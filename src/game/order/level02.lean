import data.real.basic

/-
# Chapter 2 : Order

## Level 2

This level invites you to work out a property of the absolute value.
In Lean the absolute value of $x$ is denoted by `abs x`. 
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
