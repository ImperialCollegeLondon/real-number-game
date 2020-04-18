import game.series.L01defs

/- 
Temporary level 01: If $\sum a_n$ converges, then $a_n \to 0$.
-/

/- Lemma
If partial sum sequence of $a_n$ convergent, $a_n → 0$.
-/
lemma sum_converges (a : ℕ → ℝ) : 
    is_convergent (partial_sum_sequence a) \to is_limit a 0 :=
begin
    sorry,
end
