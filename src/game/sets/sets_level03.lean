import game.sets.sets_level02 -- hide

namespace xena -- hide

variable X : Type -- hide

/-
# Chapter 1 : Sets

## Level 3
-/


/- 
Now prove that for any two sets $A$ and $B$, $A ∩ B ⊆ A$.
   
The definition of `x ∈ A ∩ B` is `x ∈ A ∧ x ∈ B`.

This should be similar to the previous exercises.
-/

/- Hint : Hint : Try changing your goal to one beginnning `∀ x : X ...`

Change our goal to one that is definitionally equivalent by using

`change ∀ x : X, (x ∈ A ∧ x ∈ B) → x ∈ A,`

and start your proof of this universally quantified expression in the usual way.

Note that the brackets are just for readability. By convention, ∧ binds more tightly than →.
-/

/- Hint : Hint : In the NNG you learned a specific tactic for dealing with hypotheses of form P ∧ Q

Introduce simultaneously an element of arbitrary type X, and the hypothesis of our implication, using

`intros x hx,`

Now use the `cases` tactic on our hypothesis, giving appropriate names to the two projections

`cases hx with xA xB`,

and finish with an `exact`.
-/


/- Lemma
If $A$ and $B$ are sets of any type $X$, then
$$ A \cap B \subseteq A.$$
-/
theorem intersection_subset (A B : set X) : A ∩ B ⊆ A  :=
begin
  rw subset_iff,
  intros x hx,
  rw mem_inter_iff at hx,
  tauto!, -- or cases, assumption
end

end xena -- hide
