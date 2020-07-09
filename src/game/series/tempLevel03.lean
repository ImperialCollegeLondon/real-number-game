import game.series.tempLevel02
variable X : Type --hide

namespace xena

/- 
Idea 03: comparison test
-/

/- Lemma
Suppose $0 ≤ a_n ≤ b_n$ for all n ∈ ℕ. If $∑ b_n$ converges
then $∑ a_n$ converges and $∑ a_n ≤ ∑ b_n$.
-/

theorem comparison_test (a b : ℕ → ℝ) 
(h1 : ∀ (n : ℕ), 0 ≤ a n)
(h2 : ∀ (n : ℕ), a n ≤ b n) : 
series_converges b → series_converges a :=

begin

--introduce hyp that series over b converges, with sum S
intro hyp,

-- we will use the following fact later
-- our converging sequence of partials must be bounded
have fact := bounded_if_convergent (seq_partials_over b) hyp,

cases hyp with S hypS,
    
    --show that partial sums over a are all positive
    have fact1: ∀ k : ℕ, (0 ≤ kth_partial_sum a k),
    unfold kth_partial_sum, -- just making finset explicit
    intro k,

        have fact2: ∀ x ∈ (finset.range (k + 1)), 0 ≤ a x,
        intros x hx,
        specialize h1 x, exact h1,
        
    apply finset.sum_nonneg,
    exact fact2,
    
    --show that nth partial sum over a ≤ nth partial sum over b
    have fact3: ∀ k : ℕ, 
    kth_partial_sum a k ≤ kth_partial_sum b k,
    intro k,
    
        have fact4: ∀ x ∈ (finset.range (k + 1)), a x ≤ b x,
        intros x hx,
        specialize h2 x, exact h2,

    apply finset.sum_le_sum,
    exact fact4,    
    
-- Although we know that our series over b converges with sum S
-- we use the fact that the sequence of sums must be bounded 
-- by *some* T (i.e. we don't use the fact that S is the supremum)

cases fact with T hypT,
-- hypT is stated in terms of `abs`
-- so our partial sums over b are bounded above 
have fact5: ∀ k : ℕ, kth_partial_sum b k ≤ T,
unfold seq_partials_over at hypT,
intro K,
have fact6: kth_partial_sum b K ≤ |kth_partial_sum b K|,
exact le_abs_self (kth_partial_sum b K),
have :=  hypT K,
linarith,
-- so our partial sums over a are bounded above 
have fact7 : ∀ k : ℕ, kth_partial_sum a k ≤ T,
intro k, specialize fact3 k, specialize fact5 k, linarith,
-- bdd_mono_converges is the relevant theorem now.
-- but it uses absolute values, so we will need to
-- do a little more work using some facts proved above
refine bdd_mono_converges (seq_partials_over a) _ _,
unfold seq_partials_over,
use T,
intro m,
let fact8 := fact7 m,
refine max_le (fact7 m) _,
have fact9 := fact1 m,
linarith,

unfold is_monotone,
left,
intro n,
unfold seq_partials_over,
let fact10 := finset.sum_range_succ a (n+1),
have fact11 := h1 (n + 1), 
unfold kth_partial_sum,
linarith,

end

end xena