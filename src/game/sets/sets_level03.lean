import game.sets.sets_level02 -- hide

namespace xena -- hide

open_locale classical -- hide

variable X : Type -- hide

/-
# Chapter 1 : Sets

## Level 3 : intersection (∩)
-/


/- 
Now prove that for any two sets $A$ and $B$, $A ∩ B ⊆ A$.
   
You will need to rewrite the following term:

```
mem_inter_iff : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B 
```
-/

/- Axiom : mem_inter_iff :
x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B
-/

/- Hint : Stuck?
You need to start the same way as in the previous levels.
Try and get yourself into a situation where you have a
*hypothesis* `hAB : x ∈ A ∩ B` and then use `rw mem_inter_iff at hAB`. 
-/

/- Hint: A note on `x ∈ A ∧ x ∈ B → x ∈ A`
By convention, ∧ binds more tightly than →
(i.e. `x ∈ A ∧ x ∈ B → x ∈ A` means `(x ∈ A ∧ x ∈ B) → x ∈ A`)
-/

/- Hint : Reminder about `cases` 
The `cases h with hP hQ` tactic turns `h : P ∧ Q` into `hP : P` and `hQ : Q`
-/

/- Hint : The `tauto!` tactic
The `tauto!` tactic solves goals in propositional logic (i.e. problems where
the relevant hypotheses and goal just involve `∧`, `∨`, `¬` and `→` and
propositions -- for example it could easily solve this goal:

```
h : P ∧ Q
⊢ P
```
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
