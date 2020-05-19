import data.set.basic
import tactic.ext
import tactic.tauto


namespace xena -- hide

variable X : Type
/-
# Chapter 1 : Sets

## New level 5/6?
-/


/-
See if you can prove the identity below using the `ext` tactic.

Applying `ext` with no arguments will apply as many *extensionality* lemmas
as Lean can find.
-/

/- Hint : Propositional Extensionality 

`(a ↔ b) → a = b`

If two propositions imply one another, then those two propositions are equal.
-/

/- Hint : Function Extensionality

`(∀ (X : α), f₁ x = f₂ x → f₁ = f₂`

If two functions agree on all arguments, then those functions are equal.

-/

/- Hint : Set Extensionality

`(∀ (z : Set), z ∈ x ↔ z ∈ y) → x = y`

Two sets are equal if and only if they contain the same elements.

-/

/-
For example, `ext` will reduce a goal `S = T` to a goal `∀x (x ∈ S ↔ x ∈ T)`.
This makes `ext` especially useful for proving identities.

For this level, you need to know that the *complement* of a set `A` is denoted `-A` (usually $A^{c}$ in
textbooks). It is the set of 
all elements *not* in `A`. 
In Lean this is defined in terms of a universal set `univ` containing 
all and only the elements of the domain (here, X).

Given two sets `A` and `B`, the *set
difference* `A \ B` is the set of all elements that are in `A` but not in `B`.

-/

/- Hint : Hint : 

A goal of `x ∈ -A` is definitionally equal to a goal of `x ∉ A`.

-/

/- Lemma
If $A$ and $B$ are sets with elements of type $X$, then

$$(A \setminus B) = A \cap B^{c}.$$

-/
theorem compdiff_eq_comp_union (A B : set X) : A \ B = A ∩ -B := 
begin
ext,
    split, 
    {   intro h1,         
        split,
           {  cases h1 with p q,
              exact p
           },
           {  cases h1 with p q,
              exact q,
           }
    },     
    {   intro h2,         
        exact h2
    }
end


end xena -- hide
