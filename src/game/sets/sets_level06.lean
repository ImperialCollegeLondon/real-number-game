import game.sets.sets_level05 -- hide
import tactic -- hide


namespace xena -- hide

variable X : Type
/-
# Chapter 1 : Sets

## Level 6
-/


/-
See if you can prove the identity below using the `ext` tactic.

Applying `ext,` with no arguments will apply as many *extensionality* lemmas
as Lean can find. The following extensionality theorems can be found in mathlib.
-/

/- Hint : Propositional Extensionality 

`constant propext {a b : Prop} : (a ↔ b) → a = b`


If two propositions imply one another, then those two propositions are equal. Here `constant` indicates that this is not just a theorem but an axiom.

Curly braces indicate that the arguments of `propext` may be left implicit and inferred from context.
-/

/- Hint : Function Extensionality

`theorem funext {f₁ f₂ : Π x : α, β x} (h : ∀ x, f₁ x = f₂ x) : f₁ = f₂.`

If two functions agree on all arguments, then those functions are equal.

-/

/- Hint : Set Extensionality

`theorem ext_iff {s t : set α} : s = t ↔ ∀ x, x ∈ s ↔ x ∈ t`


Two sets are equal if and only if they contain the same elements.

-/

/-
For example, `ext` will reduce a goal `S = T` to a goal `∀x (x ∈ S ↔ x ∈ T)`.
This makes `ext` especially useful for proving identities.

For this level, you need to know that the *complement* of a set `A` is denoted `-A` (usually $A^{c}$ in
textbooks). It is the set of 
all elements *not* in `A`. 
In Lean this is defined in terms of a universal set `univ` containing 
all and only the elements of the domain (here, all members of X).

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
theorem setdiff_eq_intersect_comp (A B : set X) : A \ B = A ∩ -B := 
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
