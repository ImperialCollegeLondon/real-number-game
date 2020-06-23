import game.sets.sets_level01 -- hide

namespace xena -- hide

open_locale classical -- hide

variable X : Type -- hide

/-
# Chapter 1 : Sets

## Level 2 : union (∪)
-/

/- 
Working with sets is very similar to working with propositions.
Let's now prove that any set $A$ is included in its union with 
any other set $B$, or $A ⊆ A ∪ B$. To work with unions you will
need to know the property which classifies them:

```
mem_union_iff : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B
```

You need to get yourself into a situation where the left hand side
of `mem_union_iff` is in your goal; that way, you can `rw mem_union_iff`
and make progress.
-/

/- Axiom : mem_union_iff :
x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B
-/

/- Hint : Tactic tip : intros
`intros` is like `intro` but can be used to introduce more than one
thing at once. For example if your goal is `⊢ ∀ (x : X), x ∈ A → x ∈ A ∪ B`
then `intros x hx` will do the same as `intro x, intro hx`.
-/

/- Hint : Stuck?
We start with a rewrite (see level 1).
Then, after introducing your terms, you'll be able to pull off
the second rewrite. Finally, you'll need to prove the `left`
side of an `or` goal.
-/


/- Lemma
If $A$ and $B$ are sets of any type $X$, then
$$ A \subseteq A\cup B.$$ 
-/
theorem subset_union_left (A B : set X) : A ⊆ A ∪ B :=
begin
  rw subset_iff,
  intros x hxA,
  rw mem_union_iff,
  left,
  assumption,
end

end xena --hide
