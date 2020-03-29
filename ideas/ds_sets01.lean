import data.real.basic
variable α : Type

lemma set_equivalence1 (A : set α) (B : set α) : A ⊆ B ↔ A ∪ B = B := 
begin
    split,
    intro H,
    change ∀ x ∈ A, x ∈ B at H,
    apply set.subset.antisymm,
    intros x hx,
    cases hx with hxA hxB,
    exact H x hxA, exact hxB,
    intros x hx, right, exact hx,
    intro H, intros x hx,
    have G : x ∈ A ∪ B, left, exact hx,
    rw H at G, exact G, done
end

lemma set_equivalence2 (A : set α) (B : set α) : A ⊆ B ↔ A ∩ B = A := 
begin
    split,
    intro H, apply set.subset.antisymm,
    intros x hx, cases hx with hA hB, exact hA,
    intros x hx, split, exact hx, exact H hx,
    intro H, intros x hx, 
    have G : x ∈ A ∩ B, rw H, exact hx,
    cases G with hA hB, exact hB, done
end