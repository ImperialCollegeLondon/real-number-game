import game.series.L01defs

/- 
Idea 03: comparison test
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
