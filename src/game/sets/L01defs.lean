import data.real.basic -- imports the real numbers ℝ
namespace xena -- hide

variable X : Type

-- World name : Sets

/-
# Chapter 1 : Sets

This chapter assumes you are familiar with the following tactics: `intro`, `apply`, `exact`. 
-- TODO -- any more?
If you are not, try playing Function World and Proposition World of the Natural Number Game. 
In this level we will learn about the `change` tactic, and the idea of definitional equality.

# Level 1 : Introduction to sets.

For our initial examples, we'll use sets with members of a generic type
$X$. Thus, let $A$ and $B$ be sets of any type $X$. Lean defines $A\subseteq B$ to mean 
$$\forall a, a \in A \implies a \in B.$$ 
Let's learn how to prove that $A \subseteq A$.

In the lemma below, our goal is `⊢ A ⊆ A`. By *definition* this means `∀ a : X, a ∈ A → a ∈ A.` 
This is the actual definition of `⊆` in Lean. 
You can check this for yourself by using the `change` tactic. 
If you start your proof with 

`change ∀ a : ℝ, a ∈ X → a ∈ X,`

then the goal will change to `⊢ ∀ (a : X), a ∈ A → a ∈ A`. You can change it back with

`change A ⊆ A,`

The `change` tactic can be used to change the goal to something *definitionally equivalent* 
to the goal. That is, something *equal by definition*. 

To make progress with a `∀ a, ...` goal you can `intro a`. You can probably take it from here.
Note that you do not have to use the `change` tactic at all, you can start with `intro a`.
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

/-
Mathematicians can be very vague about definitions. They prove
that $P \iff Q$ and then they define `foo` to mean "$P$, or equivalently $Q$, they're the same". 
In Lean you have to make one choice for a definition. 
-/

/- Tactic : refl

## Summary

`refl` proves goals of the form `X = X`.

## Details

The `refl` tactic will close any goal of the form `A = B`
where `A` and `B` are *exactly the same thing*.

### Example:
If it looks like this in the top right hand box:
```
a b c d : mynat
⊢ (a + b) * (c + d) = (a + b) * (c + d)
```

then

`refl,`

will close the goal and solve the level. Don't forget the comma.

-/

end xena
