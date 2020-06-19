import game.series.L01defs

namespace xena 

-- begin hide
-- if we want to use sigma notation, use 
-- import algebra.big_operators
-- open_locale big_operators 
-- https://leanprover-community.github.io/mathlib_docs/algebra/big_operators.html
-- end hide

/- 
If $\sum a_n$ converges, then $a_n \to 0$.

We take the approach of showing that $(S_n) → M$ then $(S_{n+1}) → M$,
and then using the fact that $a_{n+1} = S_{n+1} - S_n$.
-/

def kth_partial_sum (a : ℕ → ℝ) (k : ℕ) := (finset.range (k+1)).sum a

def seq_partials_over (a : ℕ → ℝ ) : ℕ → ℝ := (λ (n : ℕ), kth_partial_sum a n )

def series_converges (a : ℕ → ℝ) := is_convergent (seq_partials_over a)

/- Lemma
If partial sum sequence of $a_n$ convergent, $a_n → 0$.
-/

lemma seqlim_0_if_sum_converges (a : ℕ → ℝ) : 
      series_converges a → is_limit a 0 :=

begin

intro h,
cases h with M Mislimit,

-- shift_rule to show that shifted sequence of partial sums also tends to M
have fact := shift_rule (seq_partials_over a) 1 M,
have fact2 := iff.mp fact Mislimit,

-- express `a (m+1)` using partial sums, sum_range_succ seems best way
have fact3 : ∀ m : ℕ, kth_partial_sum a (m+1) 
= a (m+1) +  kth_partial_sum a (m),
intro m, from finset.sum_range_succ a (m+1),

--we really want fact4, but sum_range_succ couldn't do it directly?
have fact4 : ∀ (m : ℕ), a (m + 1) = kth_partial_sum a (m+1) - kth_partial_sum a (m),
intro n,              
specialize fact3 n,   -- do I need to do this to reorganise inside quantiifer?
linarith,       

-- we can rewrite our goal in terms of `a` shifted by +1
have fact5 : is_limit a 0 ↔ is_limit (λ (m : ℕ), a (m+1)) 0,
     from shift_rule a 1 0,
rw fact5,

have fact6: 
(λ (n : ℕ), a (n + 1)) = λ (n: ℕ), (kth_partial_sum a (n + 1) - kth_partial_sum a n),
exact funext fact4,  -- suggest gave me this!

rw fact6,

unfold seq_partials_over at Mislimit fact2, -- just for clarity

have fact7 := lim_linear 
(λ (n : ℕ), kth_partial_sum a (n + 1))
(λ (n : ℕ), kth_partial_sum a n)
M M 1 (-1) fact2 Mislimit,

simp at fact7,
exact fact7,

end

end xena
