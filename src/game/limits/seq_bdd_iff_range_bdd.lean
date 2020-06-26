import game.limits.shift_rule_seq

namespace xena --hide 

/- 
Bounded monotone sequences converge
-/

/- Lemma
It is obvious that a sequence of real numbers is bounded if and only if 
the set of its terms is bounded above and bounded below in ℝ. For that
reason you may wish to skip the proof of the following proposition, which 
we will use in our proof of the monotone convergence theorem.
-/

theorem seq_bdd_iff_range_bdd (a : ℕ → ℝ) : is_bounded a ↔ 
is_bdd_above (set.range a) ∧ is_bdd_below (set.range a):=
begin
-- first split the iff
split,
    -- Sequence bounded only if range bounded above and below (→)
    {
    -- let |a n| ≤ B for any n, from def of bounded sequence
    intro hyp,
    cases hyp with B hypB,
    -- now split the conjunction
    split,
        -- first prove set of terms is bounded above
        {
        use B,
        -- let s be any element in our set of terms
        intros s hyp,
        -- by definition of set.range, hyp proves ∃ (k : ℕ), a k = s,
        cases hyp with k hypk,
        specialize hypB k,
        -- establish a simple fact and use linarith
        have fact: a k ≤ |a k|, from le_abs_self (a k),
        linarith,
        },
        -- set of terms is bounded below, similar proof
        {
        use -B,
        intros s hyp,
        cases hyp with k hypk,
        specialize hypB k,
        refine neg_le.mp _,   -- makes goal a litle clearer
        have fact:= neg_le_abs_self (a k),
        linarith,
        }
    },
    -- Sequence bounded if range bounded above and below (←)
    intro hyp,
    -- set up our upper and lower bounds for the range
    cases hyp.left with U hypU,
    cases hyp.right with L hypL,
    -- Use max and abs to define a term B to bound our sequence
    let B := max U (|L|),
    use B,
    -- Now show that this B is a bound
    intro k,
    -- k defines an arbitrary term a k in our sequence
    have fact: a k ∈ set.range a, exact set.mem_range_self k,
    -- we know that U and L are upper and lower bounds for the range 
    have Upperbound: a k ≤ U, from hypU (a k) fact,
    have Lowerbound: L ≤ a k, from hypL (a k) fact,
    -- refine unfolds consequences of the `max` function hidden 
    -- inside `B` in our goal (I used `suggest` here)
    refine le_max_iff.mpr _,
    -- to prove |a k| ≤ B, we proceed by cases on the sign of a k 
    by_cases sign : 0 ≤ a k, 
    -- a k is non-negative, so the corresponding bound is U
    {-- so choose `left`
    left,
    have: |a k| = a k, from abs_of_nonneg sign,
    linarith,
    },
    -- a k is negative, so the corresponding bound is |L|
    -- again, prepare simple facts about `abs` and use linarith
    {
    right,
    simp at sign,
    have fact1:= abs_of_neg sign,
    have Lisneg:= lt_of_le_of_lt Lowerbound sign,
    have fact2:= abs_of_neg Lisneg,
    linarith,
    }
end


end xena -- hide
