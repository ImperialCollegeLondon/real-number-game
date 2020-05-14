import data.real.basic -- imports the real numbers ℝ
namespace xena -- hide

variable X : Type -- hide

-- World name : Sets

/-
# Chapter 1 : Sets

## Level 1 : Introduction to sets.

This chapter assumes you are familiar with the following tactics: `intro`, `apply`, `exact`, `cases` and `split`.<br>
If you are not, try playing Function World and Proposition World of the Natural Number Game.
 
In this level we will learn about the `change` tactic, and the idea of definitional equality.

For our initial examples, we'll use sets $A$ and $B$  with members of a generic type $X$. Lean defines $A \subseteq B$ to mean 
$$\forall a, a \in A \implies a \in B.$$ 
Let's learn how to prove that $A \subseteq A$, indicated as our goal in the lemma below by `⊢ A ⊆ A`. 

By *definition* our goal is equivalent to `∀ a : X, a ∈ A → a ∈ A` (this is the actual definition of `⊆` in Lean). <br>
We can use the `change` tactic to change a goal to a *definitionally equivalent* statement. <br> 
For example, if `P` and `Q` are  *equal by definition* then `change Q,` can be used to replace a goal `P` by a goal `Q`.
-/

/- Hint : Hint : If you are unsure how to prove A ⊆ A directly, try changing your goal.
If you start your proof with 

`change ∀ a : X, a ∈ A → a ∈ A,`

then the goal will change to `⊢ ∀ (a : X), a ∈ A → a ∈ A`. You can change it back with

`change A ⊆ A,`

Note that you do not have to use the `change` tactic at all to complete this proof.

-/

/-
To make progress with a goal of form `∀ a : X, ...`, we can introduce a term of type `X` by using a familiar tactic. We use this tactic when  we assume a hypothesis (to prove an implication), or when we choose an arbitrary element of a domain (to define a function).
-/

/- Hint : Hint : This tactic should be familiar from the Natural Number Game.
In this example, using

`intro a,`

will introduce an arbitrary term of type X.

Use the same tactic to introduce an appropriately named hypothesis for an implication (which will be visible if you changed the goal).

Close the goal with the `exact` tactic.
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
