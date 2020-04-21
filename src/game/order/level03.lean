import data.real.basic

/-
# Chapter 2 : Order

## Level 3

Another property of the absolute value.
-/

notation `|` x `|` := abs x --hide

/- Lemma
For any two real numbers $a$ and $b$, we have that
$$|a| ≤ c ↔ -c ≤ a ≤ c$$.
-/
theorem abs_le_rng (a c : ℝ) (h : 0 ≤ c): |a| ≤ c → (-c) ≤ a ∧ a ≤ c :=
begin
    sorry,
end
