variable α : Type -- hide

/- 
Working with sets is very similar to working with propositions.
For our initial examples, we'll use sets with members of a generic type
$α$. Let's first prove that any set $A$ is included in its union with 
any other set $B$. That is, you need to prove that:
$∀ x ∈ A, x ∈ A ∪ B$
a statement which is definitionally equivalent to the goal in the theorem.
You can actually convince yourselves that this is the case by typing
"change ∀ x ∈ A, x ∈ A ∪ B,"
just after "begin". The goal will change to the new statement. This kind of goal change
is only possible for completely equivalent, in a strict sense, goals
(i.e. goals defined to be the same).
With or without the "change" line then, you can thus introduce the 
hypotheses by "intros x hx,". Now the equivalence with the world of propositions 
will become apparent. The union of two sets is in fact the disjunction 
$P ∨ Q$ of two propositions, where the left term $P$ is $x ∈ A$. Thus, 
choosing "left," will select that term, which is our hypothesis "hx". 
You can now finish the proof with "exact hx,"
-/



theorem included_in_union (A B : set α) : A ⊆ A ∪ B :=
begin
    --change ∀ (x : α), x ∈ A → x ∈ A ∪ B,  --they may want to do this
    intros x hx,
    left, exact hx, done
end