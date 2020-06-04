import game.sets.sets_level03 -- hide

namespace xena -- hide

variable X : Type --hide

/-
# Chapter 1 : Sets

## Level 4
-/

/- Axiom : lemma eq_iff : A = B ↔ ∀ x : X, x ∈ A ↔ x ∈ B
-/

/-

To prove that two sets are equal, one needs to use the axiom
of extensionality: two sets are equal if and only if they have
the same elements.

We have called this axiom `eq_iff`. In mathlib it is called `ext_iff`.

```
lemma eq_iff : A = B ↔ ∀ x : X, x ∈ A ↔ x ∈ B
```

/- Hint : Hint -/
To prove the theorem below, remember that you can use `split` to 
change the goal into two goals, corresponding to the left-right and
right-left implication, respectively. For the first goal, after
`intro H,` the equality of the two sets can be manipulated
using `rw eq_iff`.

## A word on coding style

After a `split` statement, one goal turns into two. A good programming style
would be to use `{}` brackets to work on each goal individually, like this:
```
begin
  split,
  { insert,
    proof of,
    first goal
  },
  { insert,
    proof of,
    second goal
  }
end
```

This way you only ever have one goal to work on, and your code becomes
easier to read.
-/

/- Lemma
If $A$ and $B$ are sets of any type $X$, then
$$ A \subseteq B \iff A \cup B = B.$$
-/
theorem subset_iff_union_eq (A : set X) (B : set X) : A ⊆ B ↔ A ∪ B = B := 
begin
  rw subset_iff,
  split,
  { intro h,
    rw eq_iff,
    intro x,
    rw mem_union_iff,
     -- can't rewrite under a binder
    specialize h x, -- or replace h := h x,
    tauto! },
  { intro h,
    intros x hA,
    rw ←h,
    rw mem_union_iff,
    tauto!
  }
end

/- Hide 
theorem subset_iff_union_eq' (A : set X) (B : set X) : A ⊆ B ↔ A ∪ B = B := 
begin
  rw subset_iff,
  rw eq_iff,
  apply forall_congr,
  intro x,
  rw mem_union_iff,
  tauto!,
end
-/


end xena --hide
