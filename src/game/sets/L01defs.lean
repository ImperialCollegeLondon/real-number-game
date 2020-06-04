import data.set.basic

import kb_defs

namespace xena -- hide

variable X : Type -- we will think of X as a set here

-- begin hide
/- The first level, originally written by KMB. -/
-- end hide

/-
# Chapter 1 : Sets

## Level 1 : Introduction to sets.

This chapter assumes you are familiar with the following tactics:
`rw`, `intro`, `apply`, `exact`, `cases`, `split`, `left`, `right` and `exfalso`.<br>

(TODO (kmb) : check this list is exhaustive)

If you are not, try playing Function World and Proposition World of the Natural Number Game.

## Sets in Lean

In this world, there will be an ambient "big" set `X` (actually `X` will be a type),
and we will consider subsets of `X`. The type of subsets of `X` is called `set X`.
So if you see `A : set X` it means that `A` is a subset of `X`.

## subsets (⊆) and `subset_iff`

If `A B : set X` (i.e. `A` and `B` are subsets of `X`), then `A ⊆ B` is a
Proposition, i.e. a true/false statement. Lean knows the following fact:

```
subset_iff : A ⊆ B ↔ ∀ x : X, x ∈ A → x ∈ B
```

Let's see if you can prove `A ⊆ A` by rewriting `subset_iff`.
-/

/- Axiom : subset_iff
A ⊆ B ↔ ∀ x : X, x ∈ A → x ∈ B
-/


/- Hint : Hint
To make progress with a goal of form `∀ a : X, ...`, introduce a term of type `X` by using a familiar tactic. 

In this example, using

`intro a,`

will introduce an arbitrary term of type X.

Note that this is the tactic we use to assume a hypothesis (when proving an implication), or to choose an arbitrary element of some domain (when defining a function).

Use the same tactic to introduce an appropriately named hypothesis for an implication, and close the goal with the `exact` tactic.
-/

/-
If you get stuck, you can click on the hints for more details!
-/



/- Lemma
If $A$ is a set of elements of type X, then $A \subseteq A$. 
-/
lemma subset.refl (A : set X) : A ⊆ A :=
begin
  rw subset_iff,
  intros x h,
  exact h
end


end xena --hide
