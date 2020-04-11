variable X : Type -- hide

/- 
Now prove that for any set $A$, $A ∩ B ⊆ A$.  
After "intros x hx,", the "hx" hypothesis will be a conjunction.  
Using "cases hx with xA xB," will split it into the two hypotheses that are 
simultaneously valid.
You should be able to easily finish the proof now.
-/


/- Lemma
If $A$ and $B$ are sets of any type $X$, then
$$ A \cap B \subseteq A.$$
-/
theorem included_intersection (A B : set X) : A ∩ B ⊆ A  :=
begin
    intros x hx,
    cases hx with xA xB,
    exact xA, done
end
