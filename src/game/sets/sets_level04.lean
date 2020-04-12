import data.set.basic --hide
variable X : Type --hide

/-
You should now be able to prove the theorem below if you remember 
to use "split" and "cases" together with "apply set.subset.antisymm,".
-/

/- Lemma
If $A$ and $B$ are sets of any type $X$, then
$$ A \subseteq B \iff A \cap B = A.$$
-/
theorem included_iff_intersection (A : set X) (B : set X) : A ⊆ B ↔ A ∩ B = A := 
begin
    split,
    intro H, apply set.subset.antisymm,
    intros x hx, cases hx with hA hB, exact hA,
    intros x hx, split, exact hx, exact H hx,
    intro H, intros x hx, 
    have G : x ∈ A ∩ B, rw H, exact hx,
    cases G with hA hB, exact hB, done
end
