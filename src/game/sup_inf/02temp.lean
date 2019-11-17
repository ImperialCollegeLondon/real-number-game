import data.real.basic -- imports the real numbers ℝ
namespace xena -- hide

-- World name : Sup and Inf

/-
# Chapter 1 : Sup and Inf

# Level 1 : Introduction to sets of reals.

Let $X$ be a set of real numbers.

We say a real number $b$ is an *upper bound* for $X$ if every $x\in X$ is at most $b$.
-/
def is_upper_bound (X : set ℝ) (b : ℝ) := ∀ x : ℝ, x ∈ X → x ≤ b
/-
Here is an easy fact about upper bounds, which we shall prove below: 
If $Xsubseteq Y$ are two sets of reals, and $b$ is an upper bound for $Y$, then it's also an upper bound for $X$.

To prove this in Lean, it helps to understand a bit more about definitions. Initially our goal is
`is_upper_bound Y b → is_upper_bound X b`

-/
/- Lemma
If $Xsubseteq Y$ are two sets of reals, and $b$ is an upper bound for $Y$, then it's also an upper bound for $X$.
-/
lemma upper_bounds_mono (X Y : set ℝ) (h1 : X ⊆ Y) (b : ℝ) : is_upper_bound Y b → is_upper_bound X b :=
begin
  intro h2,
  intro a,
  intro ha,
  apply h2,
  change ∀ a, a ∈ X → a ∈ Y at h1,
--  unfold has_subset.subset set.subset at h1,
  apply h1,
  exact ha,
end
/- Tactic : refl

## Summary

`refl` proves goals of the form `X = X`.

## Details

The `refl` tactic will close any goal of the form `A = B`
where `A` and `B` are *exactly the same thing*.

### Example:
If it looks like this in the top right hand box:
```
a b c d : mynat
⊢ (a + b) * (c + d) = (a + b) * (c + d)
```

then

`refl,`

will close the goal and solve the level. Don't forget the comma.

-/

end xena
