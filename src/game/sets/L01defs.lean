import data.set.basic

namespace xena -- hide

variable X : Type -- hide

-- begin hide
/- The first level, originally written by KMB. -/
-- end hide

/-
# Chapter 1 : Sets

## Level 1 : Introduction to sets.

This chapter assumes you are familiar with the following tactics: `intro`, `apply`, `exact`, `cases`, `split`, `left` and `right`.<br>
If you are not, try playing Function World and Proposition World of the Natural Number Game.
 
In this level we will learn about the `change` tactic, and the idea of definitional equality.

For our initial examples, we'll use sets $A$ and $B$  with members of a generic type $X$. Lean defines $A \subseteq B$ to mean 
$$\forall a, a \in A \implies a \in B.$$ 
Let's learn how to prove that $A \subseteq A$, indicated as our goal in the lemma below by `⊢ A ⊆ A`. 

By *definition* our goal is equivalent to `∀ a : X, a ∈ A → a ∈ A` (that is, due to the actual definition of `⊆` in Lean). <br>
Whenever two expressions are *definitionally equal* in this way, we can use the `change` tactic to replace one by the other in a goal. <br> 
For example, if `P` and `Q` are  equal by definition then we can use

`change Q,`

to change a goal `P` to a goal `Q` (remembering the comma!).
-/

/- Hint : Hint : If you are unsure how to prove A ⊆ A directly, try changing your goal.
If you start your proof with 

`change ∀ a : X, a ∈ A → a ∈ A,`

then the goal should change to `⊢ ∀ (a : X), a ∈ A → a ∈ A`. You can change it back with

`change A ⊆ A,`

Note that you do not have to use the `change` tactic at all to complete this proof.

-/

/- Hint : Hint : To make progress with a goal of form `∀ a : X, ...`, introduce a term of type `X` by using a familiar tactic. 

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
  change ∀ a : X, a ∈ A → a ∈ A,
  intro a,
  intro ha,
  exact ha,

end


end xena --hide
