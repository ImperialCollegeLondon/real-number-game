import game.limits.seq_bdd_iff_range_bdd

namespace xena --hide 

/- 
Bounded monotone sequences converge
-/

def is_increasing (a : ℕ → ℝ) := ∀ n : ℕ, a n ≤ a (n+1)
def is_decreasing (a : ℕ → ℝ) := ∀ n : ℕ, a (n + 1) ≤ a n
def is_monotone (a : ℕ → ℝ) := is_increasing a ∨ is_decreasing a

-- begin hide
-- Note: later I need (N0 ≤ k) → (a N0 ≤ a k) for `a` monotone increasing
-- So perhaps first prove the following by induction?
theorem is_increasing' (a : ℕ → ℝ) : is_increasing a ↔ ∀ m n : ℕ, 
 m ≤ n ↔ a m ≤ a n := 
begin
sorry,
end
-- end hide

/- Lemma
Bounded monotone sequences converge. 
-/

theorem bdd_mono_converges (a : ℕ → ℝ) (h1 : is_bounded a) (h2 : is_monotone a): 
is_convergent a :=
begin
-- As before, M is the set of terms of our sequence a
let M := set.range a,

-- The increasing and the decreasing cases will be similar
cases h2 with increasing decreasing,
    
    -- monotone increasing case
    {
    have fact1: has_lub M,
    -- We use the completeness axiom (least upper bound property)
    -- to show that M has a sup. refine produces two subgoals that we 
    -- will need to prove to show that the sup exists.
    refine lub_property_reals M _,

    split,
        -- As our sequence `a` is a function from the nonempty set ℕ, 
        -- its range is nonempty
        {
        exact set.range_nonempty a,
        },
        -- We use the → (.mp) direction of our previous `trivial` lemma 
        -- to prove that M is bounded above
        {exact ((seq_bdd_iff_range_bdd a).mp h1).left,
        },

    -- So M has a lub, call it s.
    cases fact1 with s hyp_s,
    
    -- It seems reasonable to assume that s is the limit of a
    use s,
    intros e hype,

    -- We show that s - e cannot be an upper bound for M (our set of terms)
    have fact2: ¬ is_upper_bound M (s - e),
    by_contradiction claim,
    -- hyp_s.right says if y is any upper bound of M, then s ≤ y 
    -- (supremum condition)
    let forcontra := hyp_s.right (s - e) claim,
    --forcontra says that s ≤ s - e. But e is positive, so linarith closes.
    linarith,

    unfold is_upper_bound at fact2,
    push_neg at fact2,
    cases fact2 with l hypl,
    -- hypl.right is a proof that s - e < l, for some l ∈ M
    -- we want l expressed in the form a N0 for some N0,
    cases hypl.left with N0 hypN0,
    use N0,
    intros k hypk,
    
    rw is_increasing' at increasing, -- is this necessary?
    have fact3:= (increasing N0 k).mp hypk,
    refine abs_lt.mpr _,
    split, 
    linarith,
    have fact4: a k ≤ s, 
    exact hyp_s.left (a k) (set.mem_range_self k),
    linarith,
    },

    --monotone decreasing case
    {
       
    sorry,
    },

end

end xena -- hide
