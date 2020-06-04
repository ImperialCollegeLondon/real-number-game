import tactic --hide

import game.sets.sets_level06 -- hide

variable X : Type --hide

open_locale classical -- hide

namespace xena -- hide

/-
# Chapter 1 : Sets

## Level 7 : The empty set
-/

/-

The way to handle the empty set is the following:

```
lemma mem_empty_iff (a : X) : a ∈ (∅ : set X) ↔ false
```
-/

/- Axiom : mem_empty_iff :
a ∈ (∅ : set X) ↔ false
-/

/- Hint
Remember that `exfalso` changes any goal to `false`. This can be
convenient if your hypotheses can prove `false`.
 -/

/- Lemma
The empty set is a subset of any set $A$. 
-/
theorem empty_set_subset (A : set X) : ∅ ⊆ A :=
begin
  rw subset_iff,
  intros x hx,
  exfalso,
  rw mem_empty_iff at hx,
  exact hx,
end

end xena