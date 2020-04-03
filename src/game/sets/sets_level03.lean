import data.set.basic
variable α : Type

/-
To prove the theorem below, remember that you can use "split" to 
change the goal into two goals, corresponding to the left-right and
right-left implication, respectively. For the first goal, after
"intro H," the equality of the two sets can be rewritten in terms
of inclusion by "apply set.subset.antisymm,".
-/

theorem included_iff_union (A : set α) (B : set α) : A ⊆ B ↔ A ∪ B = B := 
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
