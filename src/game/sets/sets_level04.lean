import data.set.basic --hide
variable X : Type --hide

/- Axiom : set.subset.antisymm {A B : set X} (H : A ⊆ B) (G : B ⊆ A) : 
A = B
-/

/-
To prove the theorem below, remember that you can use "split" to 
change the goal into two goals, corresponding to the left-right and
right-left implication, respectively. For the first goal, after
"intro H," the equality of the two sets can be rewritten in terms
of inclusion by "apply set.subset.antisymm,". You can find the corresponding
statement in the left side bar.
-/

/- Lemma
If $A$ and $B$ are sets of any type $X$, then
$$ A \subseteq B \iff A \cup B = B.$$
-/
theorem subset_iff_union_eq (A : set X) (B : set X) : A ⊆ B ↔ A ∪ B = B := 
begin
    split,
    intro H,
    apply set.subset.antisymm,
    intros x hx,
    cases hx with hxA hxB,
    exact H hxA, exact hxB,
    intros x hx, right, exact hx,
    intro H, intros x hx,
    have G : x ∈ A ∪ B, left, exact hx,
    rw H at G, exact G, done
end
