import game.series.L01defs

/- 
Temporary level 01: $\sum a_n$ converges iff $a_n \to 0$.
-/

/- Lemma
Partial sum sequence of $a_n$ convergent iff $a_n → 0$.
-/
lemma sum_converges (a : ℕ → ℝ) : 
    is_convergent (partial_sum_sequence a) ↔ is_limit a 0 :=
begin
    sorry,
end
