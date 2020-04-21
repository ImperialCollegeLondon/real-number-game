import data.real.basic

/-
# Chapter 2 : Order

## Level 1

This level aims to familiarize you with the use of the trichotomy property in 
Lean, as it will come in handy in later levels.
The corresponding statement in Lean's mathlib is:

`lt_trichotomy : ∀ (a b : ?M_1), a < b ∨ a = b ∨ b < a`

and you can just use it to finish the proof below.
-/


/- Lemma
For any two real numbers $a$ and $b$, we have that
$$ a < b \lor a = b \lor b < a$$.
-/
theorem trichotomy' (a b : ℝ) : a < b ∨ a = b ∨ b < a :=
begin
    exact lt_trichotomy a b, done
end
