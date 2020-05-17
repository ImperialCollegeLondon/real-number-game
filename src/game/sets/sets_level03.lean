variable X : Type -- hide

/-
# Chapter 1 : Sets

## Level 3
-/


/- 
Now prove that for any two sets $A$ and $B$, $A ∩ B ⊆ A$.  
After `intros x hx,`, the `hx` hypothesis will be a conjunction.  
The definition of `x ∈ A ∩ B` is `x ∈ A ∧ x ∈ B`.
-/


/- Lemma
If $A$ and $B$ are sets of any type $X$, then
$$ A \cap B \subseteq A.$$
-/
theorem intersection_subset (A B : set X) : A ∩ B ⊆ A  :=
begin
    intros x hx,
    cases hx with xA xB,
    exact xA, done
end
