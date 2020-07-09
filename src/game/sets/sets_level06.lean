import game.sets.sets_level05 -- hide
import tactic -- hide


namespace xena -- hide

variable X : Type

open_locale classical -- hide

/-
# Chapter 1 : Sets

## Level 6 : `sdiff` and `neg`
-/

/-

The set-theoretic difference `A \ B` satisfies the following property:

```
lemma mem_sdiff_iff : x ∈ A \ B ↔ x ∈ A ∧ x ∉ B
```

The complement `-A` of a set `A` (often denoted $A^c$ in textbooks)
is all the elements of `X` which are not in `A`:

```
lemma mem_neg_iff : x ∈ -A ↔ x ∉ A
```

In this lemma, you might get a shock. The `rw` tactic is aggressive
in the Real Number Game -- if after a rewrite the goal can be
solved by `refl`, then Lean will close the goal automatically.

-/

/- Axiom : mem_sdiff_iff :
x ∈ A \ B ↔ x ∈ A ∧ x ∉ B
-/

/- Axiom : mem_neg_iff :
x ∈ -A ↔ x ∉ A
-/

/- Lemma
If $A$ and $B$ are sets with elements of type $X$, then

$$(A \setminus B) = A \cap B^{c}.$$
-/
theorem setdiff_eq_intersect_comp (A B : set X) : A \ B = A ∩ Bᶜ := 
begin
  rw ext_iff,
  intro x,
  rw mem_sdiff_iff,
  rw mem_inter_iff,
  rw mem_neg_iff,
end


end xena -- hide
