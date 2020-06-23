import game.sets.sets_level03 -- hide

namespace xena -- hide

open_locale classical -- hide

variable X : Type --hide

/-
# Chapter 1 : Sets

## Level 4
-/

/- Axiom : ext_iff :
A = B ↔ ∀ x : X, x ∈ A ↔ x ∈ B
-/

/-

To prove that two sets are equal, one needs to use the axiom
of extensionality: two sets are equal if and only if they have
the same elements.

In Lean's maths library this axiom is called `ext_iff`.

```
lemma ext_diff : A = B ↔ ∀ x : X, x ∈ A ↔ x ∈ B
```
-/

/- Hint: A word on coding style

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
easier to read. After `split` you might want to write 
```
{ sorry},
{ sorry}
```
so that your code has no errors while you're working on it.
-/


/- Hint : Stuck?
To prove the theorem below, remember that you can use `split` to 
change the goal into two goals, corresponding to the left-right and
right-left implication, respectively. For the first goal, after
`intro h,` the equality of the two sets can be manipulated
using `rw ext_iff`.
-/

/- Hint: rewrite failures and the `simp_rw` tactic
`rw` doesn't work "under a binder". In other words, if your goal is
`⊢	∀ (x : X), x ∈ B ↔ x ∈ A ∪ B` then `rw mem_union_iff` won't work!
It's the `∀` which is blocking it. Either do `intro x` (and then
the `rw` will work), or use a more powerful rewrite tactic
called `simp_rw`, which will work 

-/

/- Lemma
If $A$ and $B$ are sets of any type $X$, then
$$ A \subseteq B \iff A \cup B = B.$$
-/
theorem subset_iff_union_eq (A : set X) (B : set X) : A ⊆ B ↔ B = A ∪ B := 
begin
  rw subset_iff,
  split,
  { intro h,
    rw ext_iff,
     -- can't rewrite under a binder
    simp_rw mem_union_iff,
    intro x,
    specialize h x, -- or replace h := h x,
    tauto! },
  { intro h,
    intros x hA,
    rw h,
    rw mem_union_iff,
    tauto!
  }



end

--begin hide
-- theorem subset_iff_union_eq' (A : set X) (B : set X) : A ⊆ B ↔ B = A ∪ B := 
-- begin
--   rw subset_iff,
--   rw ext_iff,
--   apply forall_congr,
--   intro x,
--   rw mem_union_iff,
--   tauto!,
-- end
--end hide


end xena --hide
