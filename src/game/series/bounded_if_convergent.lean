import game.limits.L01defs
import data.finset
import game.limits.seq_convCauchy
import tactic.linarith
import data.real.basic
import algebra.pi_instances


namespace xena -- hide

notation `|` x `|` := abs x -- hide

/-
A useful result for working with sequences -- a convergent sequence is bounded.
-/

/- We define the concepts of a bound and a bounded sequence, in much the same way
that we defined the concepts of a limit and a convergent sequence. -/

definition is_bound (a : ℕ → ℝ) (M : ℝ) := ∀ n, | a n | ≤ M
definition is_bounded (a : ℕ → ℝ) := ∃ M, is_bound a M


/- Lemma
A convergent sequence is bounded.
-/
open finset
lemma bounded_if_convergent (a : ℕ → ℝ)
    (ha : is_convergent a ) : 
    is_bounded a :=
begin

cases ha with α islim,             
specialize islim 1 (by linarith),  -- specialise to the case ε = 1, linarith knows this is OK
cases islim with N_k HN_k,         -- introduce the natural N_k fulfilling ε = 1 case
   
   -- We use these to show that there is a bound for all terms with index ≥ N_k 
   -- Then take the max of this bound and the earlier terms.

have bounds_geq_N_k : ∀ n ≥ N_k, |a n| ≤ | α | + 1,    

{
intros bigN Nisbig,                 -- introduce some bigN ≥ N_k
specialize HN_k bigN,               -- specialize to bigN
have fact1:= HN_k(Nisbig),          -- just applying our conditional
rw abs_lt at fact1,    

rw abs_le,     -- note our abs_le will require us to show c ≥ 0, unlike mathlib
simp,
split,
        
    {have smallfact: - α ≤ | α | := neg_le_abs_self α,
        linarith},   
        
    {have smallfact2: α ≤ | α | := le_abs_self(α),
        linarith}, 

-- condition for abs_le
have fact: 0 ≤ |α|, from abs_nonneg α,
linarith,

},

        
   --  Having shown that we have a bound for the elements above N_k, we consider the earlier terms
   --  This section is mostly cribbed from Kevin's M1P1 limits file

   let rangeset := finset.image (abs ∘ a) (range (N_k + 1)),    -- range (N) is set of nats < N

   have fact4 : |a 0| ∈ rangeset := finset.mem_image_of_mem _ (mem_range.2 (nat.zero_lt_succ _)), 
   have fact5 : rangeset ≠ ∅ := ne_empty_of_mem fact4,        
   have fact6 := nonempty_iff_ne_empty.mpr fact5,    -- could hide this and just state nonemptiness?  
   
   let Bx := rangeset.max' fact6,                              
   let B := max Bx ( |α|  + 1),
 
use B,
intro n,
cases lt_or_ge n N_k with Hlt Hge,

    simp,
    left,        
    have HBx : ∀ n < N_k, |a n| ≤ Bx := λ n Hn, le_max' rangeset fact6 _
    (mem_image_of_mem _ (mem_range.2 (nat.lt_succ_of_lt Hn))),   
    apply HBx,               -- was the lambda the best way to do this?
    exact Hlt,         
    
    have h2 : |a n| ≤ |α| + 1 := bounds_geq_N_k n Hge,
    have h3 : |α| + 1 ≤ B := le_max_right _ _,
    linarith,
end

end xena -- hide
