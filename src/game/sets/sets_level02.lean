variable α : Type -- hide

/- 
Now prove that for any set $A$, $A ∩ B ⊆ A$.  
After "intros x hx,", the "hx" hypothesis will be a conjunction.  
Using "cases hx with xA xB," will split it into the two hypotheses that are 
simultaneously valid.
You should be able to easily finish the proof now.
-/



theorem included_intersection (A B : set α) : A ∩ B ⊆ A  :=
begin
    intros x hx,
    cases hx with xA xB,
    exact xA, done
end