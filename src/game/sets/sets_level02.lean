variable X : Type -- hide

-- World name : Sets

/-
# Chapter 1 : Sets

## Level 2
-/

/- 
Working with sets is very similar to working with propositions.
Let's now prove that any set $A$ is included in its union with 
any other set $B$. That is, you need to prove that:
`∀ x ∈ A, x ∈ A ∪ B`,
a statement which is definitionally equivalent to the goal in the theorem.
You can again convince yourselves that this is the case by typing
`change ∀ x ∈ A, x ∈ A ∪ B,`
just after `begin`. The goal will change to the new statement. 
With or without the `change` line, you can introduce the 
hypotheses by `intros x hx,`. Now the equivalence with the world of propositions 
will become apparent. The union of two sets is stated as the disjunction 
$P ∨ Q$ of two propositions, where the left one, $P$, reads $x ∈ A$. Thus, 
choosing `left,` will select the term that coincides with the hypothesis `hx`. 
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
