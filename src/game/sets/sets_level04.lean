import game.sets.sets_level03 -- hide

namespace xena -- hide

variable X : Type --hide

/-
# Chapter 1 : Sets

## Level 4
-/


/- Axiom : set.subset.antisymm {A B : set X} (H : A ⊆ B) (G : B ⊆ A) : 
A = B
-/

/-
To prove the theorem below, remember that you can use `split` to 
change the goal into two goals, corresponding to the left-right and
right-left implication, respectively. For the first goal, after
`intro H,` the equality of the two sets can be rewritten in terms
of inclusion by `apply set.subset.antisymm,`. You can find the corresponding
statement in the left side bar. 
In that statement, the arguments in between braces are implicit; 
in this case the types of $A$ and $B$ are inferred from the
two hypotheses $H$ and $G$.

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
  split,
  { intro h,
    rw eq_iff,
    intro x,
    rw mem_union_iff, -- can't rewrite under a binder
    rw subset_iff at h,
    split,
    { intro h2,
      cases h2,
      { apply h,
        assumption},
      { assumption}},
    { intro hB,
      right,
      assumption}},
  { intro h,
    rw subset_iff,
    intros x hA,
    rw ←h,
    rw mem_union_iff,
    left,
    assumption
  }
end

theorem subset_iff_union_eq' (A : set X) (B : set X) : A ⊆ B ↔ A ∪ B = B := 
begin
  rw subset_iff,
  rw eq_iff,
  apply forall_congr,
  intro x,
  rw mem_union_iff,
  tauto!,
end



-- begin
--     split,
--     intro H,
--     apply set.subset.antisymm,
--     intros x hx,
--     cases hx with hxA hxB,
--     exact H hxA, exact hxB,
--     intros x hx, right, exact hx,
--     intro H, intros x hx,
--     have G : x ∈ A ∪ B, left, exact hx,
--     rw H at G, exact G, done
-- end

end xena --hide
