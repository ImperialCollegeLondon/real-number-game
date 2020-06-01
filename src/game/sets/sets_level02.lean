import game.sets.L01defs -- hide

namespace xena -- hide

variable X : Type -- hide

/-
# Chapter 1 : Sets

## Level 2
-/

/- 
Working with sets is very similar to working with propositions.
Let's now prove that any set $A$ is included in its union with 
any other set $B$, or $A ⊆ A ∪ B$. 

Our goal is definitionally equivalent to `∀ x ∈ A, x ∈ (A ∪ B)`.
The definition of `x ∈ (A ∪ B)` is `x ∈ A ∨ x ∈ B`.

You should already know the tactics needed to prove this goal, so give 
it a try before checking the hints.
-/

/- Hint : Hint : The proof steps may become clearer if you change the goal.
Use the `change` tactic and the definitions give above:

`change ∀ x ∈ A, x ∈ A ∨ x ∈ B,`

This will change your goal to the definitionally equivalent 

`∀ x : X, x ∈ A ⇾ x ∈ A ∨ x ∈ B`

Start your proof of `∀ (x : X) ...` in the way you learned in the previous level.

You will then have a statement of propositional form `α → β ∨ γ`. See if you can use your knowledge of propositions to solve this!
-/

/- Hint : Hint : After introducing your terms, you'll need to prove the `left` side of a disjunction.
With or without the `change` lines, you can introduce the 
hypotheses we need by using 

`intros x hx,`

Now the equivalence with the world of propositions will become apparent. 

To prove that the union of two sets is inhabited is to prove the disjunction 
$P ∨ Q$ of two propositions. In this case, $P$ is our statement $x ∈ A$.

Choosing `left,` will change our goal to the first disjunct. 

You should now be able to easily finish the proof.
-/


/- Lemma
If $A$ and $B$ are sets of any type $X$, then
$$ A \subseteq A\cup B.$$ 
-/
theorem subset_union_left (A B : set X) : A ⊆ A ∪ B :=
begin
    --change ∀ (x : α), x ∈ A → x ∈ A ∪ B,  --they may want to do this
    intros x hx,
    left, exact hx, done

end

end xena --hide
