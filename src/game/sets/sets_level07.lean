import data.real.basic --hide

/-
# Chapter 1 : Sets

## Level 7
-/


/- 
This is a very basic example of working with intervals of real numbers in Lean.
An interval that is closed at both endpoints $a$ and $b$ can be 
constructed using `set.Icc a b`. For an open-closed interval, the notation
is `set.Ioc a b`, etc. The usual closed-interval notation, using square
brackets, is used here as a wrapper around these definitions.
After `intro hx,` the `split` tactic will showcase the conditions for 
membership. The inequality goals can be met with the `linarith` tactic.
The latter is very useful when dealing with goals that don't involve any
nonlinearity in the involved variables, in particular with inequalities.
-/

notation `[` a `,` b `]`  := set.Icc a b

/- Lemma
If $x = 2$ then $x ∈ [0,5]$
-/
lemma in_closed_interval (x:ℝ) : x = 2 → x ∈ [(0:ℝ), 5] := 
begin
    intro hx,
    split, linarith, linarith, done
end

