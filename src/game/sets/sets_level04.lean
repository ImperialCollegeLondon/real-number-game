import data.set.basic
variable α : Type

/-
You should now be able to prove the theorem below if you remember 
to use "split" and "cases" together with "apply set.subset.antisymm,".
-/

theorem included_iff_intersection (A : set α) (B : set α) : A ⊆ B ↔ A ∩ B = A := 
begin
    split,
    intro H, apply set.subset.antisymm,
    intros x hx, cases hx with hA hB, exact hA,
    intros x hx, split, exact hx, exact H hx,
    intro H, intros x hx, 
    have G : x ∈ A ∩ B, rw H, exact hx,
    cases G with hA hB, exact hB, done
end