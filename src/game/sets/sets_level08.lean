import kb_real_defs --hide

/-
# Chapter 1 : Sets

## Level 8
-/


/- 
This is a very basic example of working with intervals of real numbers in Lean.
An interval `[a, b]` that is closed at both endpoints $a$ and $b$ can be 
constructed using `set.Icc a b`. For an open-closed interval `(a, b]`,
the notation
is `set.Ioc a b`, etc. The usual closed-interval notation, using square
brackets, is used here as a wrapper around these definitions. We have
the following lemma:



```
mem_Icc_iff : x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b
```
-/

/- Axiom : mem_Icc_iff :
x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b
-/

/-
After rewriting it, the `split` tactic will isolate the two conditions for 
membership. Each inequality goals can be solved with the `norm_num` tactic,
which closes goals which are equalities or inequalities between explicit
real numbers.
-/

/- Pro tip : semicolons
If instead of a comma, you end a line with a semicolon, then
Lean will apply the next tactic to all the goals created by the
previous tactic, rather than just the top one.
-/

/- Pro tip : definitional equality
`mem_Icc_iff` is true by definition, so you don't actually
have to even rewrite it.
-/

notation `[` a `,` b `]`  := set.Icc a b

/- Lemma : no-side-bar
$2 ∈ [0,5]$
-/
example : (2 : ℝ) ∈ [(0 : ℝ), 5] := 
begin
    rw mem_Icc_iff,
    split;
    norm_num,
end

