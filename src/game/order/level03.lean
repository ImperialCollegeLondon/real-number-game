import data.real.basic

/-
# Chapter 2 : Order

## Level 3

Another well-known property of the absolute value.
-/

notation `|` x `|` := abs x -- hide

/- Lemma
For any two real numbers $a$ and $b$, we have that
$$| |a| - |b| | ≤ |a - b|$$.
-/
theorem abs_of_sub_le_abs (a b : ℝ) : | |a| - |b| | ≤ |a - b| :=
begin
    sorry, -- need to work it out
end
