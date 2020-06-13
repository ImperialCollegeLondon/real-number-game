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
(hyp1 : ∀ (n : ℕ), 0 ≤ a n)
 (hyp2 : ∀ (n : ℕ), a n ≤ b n) : 
series_converges b → series_converges a :=

begin

--introduce hyp that series over b converges, with sum T
intro hyp1,
cases hyp1 with T hypT,

    --show that partial sums over a are all positive
    have fact1: ∀ k : ℕ, (0 ≤ kth_partial_sum a k),
    unfold kth_partial_sum, -- just making finset explicit
    intro k,

        have fact2: ∀ x ∈ (finset.range (k + 1)), 0 ≤ a x,
        intros x hx,
        specialize hyp1 x, exact hyp1,
        
    apply finset.sum_nonneg,
    exact fact2,
    
    --show that nth partial sum over a ≤ nth partial sum over b
    have fact3: ∀ k : ℕ, 
    kth_partial_sum a k ≤ kth_partial_sum b k,
    unfold kth_partial_sum,
    intro k,
    
        have fact4: ∀ x ∈ (finset.range (k + 1)), a x ≤ b x,
        intros x hx,
        specialize hyp2 x, exact hyp2,

    apply finset.sum_le_sum,
    exact fact4,    

unfold series_converges,

have fact5: ∀ n : ℕ, kth_partial_sum a n ≤ T,
unfold seq_partials_over at hypT,
intro n,
unfold is_limit at hypT,

sorry,
sorry,
/-  
    change 0 ≤ (finset.sum (finset.range (k + 1)) a),
   
   --∑ x in s, f x is notation for finset.sum s f 

-/

end

end xena