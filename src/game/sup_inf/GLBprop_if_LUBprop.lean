import game.sup_inf.rat_complete

namespace xena --hide 

/-
# Chapter 3 : Sup and Inf

## Level 14
-/


/- 
The Least Upper Bound property implies
Greatest Lower bound Property
-/

-- begin hide
--NOTE: We have a form of the completeness axiom at Sup/Inf World
--level 13.
--Here I'll assume LUB property as an axiom, and prove it implies 
--GLB property. But perhaps `axiom` should be avoided. -- GT
-- end hide

def is_bdd_above (S : set ℝ) := ∃ x : ℝ, is_upper_bound S x    

def is_lower_bound (S : set ℝ) (x : ℝ) := ∀ s ∈ S, x ≤ s
def is_bdd_below (S : set ℝ) := ∃ x : ℝ, is_lower_bound S x
def is_glb (S : set ℝ) (x : ℝ) := is_lower_bound S x ∧ 
∀ y : ℝ, is_lower_bound S y → y ≤ x
def has_glb (S : set ℝ) := ∃ x : ℝ, is_glb S x

/-
Completeness Axiom
-/

axiom lub_property_reals (S : set ℝ) : 
(S.nonempty ∧ is_bdd_above S) → (has_lub S)

/- Lemma
LUB property implies GLB property
-/

theorem glb_property_reals (S: set ℝ) : 
(S.nonempty ∧ is_bdd_below S) → has_glb S :=

begin
intro hyp,

--define set L of lower bounds of S
let L := { x : ℝ | is_lower_bound S x},  

--anything in S is an upper bound of L
have fact1: ∀ x ∈ S, is_upper_bound L x,
intros x hypx b hypb,
exact hypb x hypx,            -- `suggest` provided this line

--hyp.left is the claim that S is nonempty. use this to show
--that L is bounded above
cases hyp.left with y hypy, 
have fact2: is_bdd_above L, use y, exact fact1 y hypy,

-- can now show that L has supremum `a`. Note direct use of hyp.right
-- (S is bounded below) as proof that L is nonempty
have fact3:= lub_property_reals L (and.intro hyp.right fact2),
cases fact3 with a hypa,

-- we now show that a is the infimum of S

use a,
split,
    -- first prove that a is a lower bound for S,
    {
    assume z hypz,
    -- given z ∈ S, we prove by contradiction that a ≤ z,
    by_contradiction claim,
    push_neg at claim,
    unfold is_lub at hypa,
    -- hypa.right says that for any upper bound y of L, a ≤ y
    let for_contra := hypa.right z (fact1 z hypz), 
    -- linarith solves our goal - claim and for_contra are contradictory.
    linarith,
    },

    -- now prove that for any lower bound x of S, x ≤ a 
    {
    intros x hypx,
    have fact: x ∈ L, exact hypx,
    -- hypa.left says that a is an upper bound of L
    exact hypa.left x hypx,
    }

end


end xena -- hide
