import data.real.basic
open real

variable X : Type -- hide

/- 
# Work in progress.

-/

#check finset
#check finset.card_range
#check list

--do we want a finset or a list?
--either way, not sure how to go about this
--def partition (a b : ℝ) (A: set.Icc a b) (n : ℕ) := finset ℝ


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
