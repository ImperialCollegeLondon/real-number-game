import game.series.L01defs
variable X : Type --hide

/- 
Idea 02: if $\forall n \in \mathbb{N}, a_n \ge 0$,
$\sum a_n$ converges iff partial sums bounded above.
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
