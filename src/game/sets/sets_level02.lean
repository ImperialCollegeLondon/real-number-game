variable X : Type -- hide

-- World name : Sets

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
The goal can be changed to the quantified statement above, using

`change ∀ x ∈ A, x ∈ A ∪ B,`

To make the relationship between sets and propositions even clearer, we could use

`change ∀ x ∈ A, x ∈ A ∨ x ∈ B,`
-/

/-
<hr style="height:10px; visibility:hidden;" />
-/

/- Hint : Hint : After introducing your terms, you'll need to prove one side of a disjunction.
With or without the `change` lines, you can introduce the 
hypotheses we need by using 

`intros x hx,`

Now the equivalence with the world of propositions will become apparent. 

To prove that the union of two sets is inhabited is to prove the disjunction 
$P ∨ Q$ of two propositions, where the left one, $P$, reads $x ∈ A$. 

Thus, choosing `left,` will select the term that coincides with the hypothesis `hx`. 

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
