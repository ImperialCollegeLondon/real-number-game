import tactic -- hide

import data.real.basic -- imports the real numbers
/-

-/
open_locale classical -- allow proofs by contradiction
/-

-/
noncomputable theory -- don't fuss about the reals being noncomputable

namespace xena -- hide

/- Tactic : cases

## Summary:

`cases` is a tactic which works on hypotheses.
If `h : P ∧ Q` or `h : P ↔ Q` is a hypothesis then `cases h with h1 h2` will remove `h`
from the list of hypotheses and replace it with the "ingredients" of `h`,
i.e. `h1 : P` and `h2 : Q`, or `h1 : P → Q` and `h2 : Q → P`. Also
works with `h : P ∨ Q` and `n : mynat`. 

## Details

How does one prove `P ∧ Q`? The way to do it is to prove `P` and to
prove `Q`. There are hence two ingredients which go into a proof of
`P ∧ Q`, and the `cases` tactic extracts them. 

More precisely, if the local context contains
```
h : P ∧ Q`
```

then after the tactic `cases h with p q,` the local context will
change to
```
p : P,
q : Q
```
and `h` will disappear. 

Similarly `h : P ↔ Q` is proved by proving `P → Q` and `Q → P`,
and `cases h with hpq hqp` will delete our assumption `h` and
replace it with
```
hpq : P → Q,
hqp : Q → P
```

Be warned though -- `rw h` works with `h : P ↔ Q` (`rw` works with
`=` and `↔`), whereas you cannot rewrite with an implication.

`cases` also works with hypotheses of the form `P ∨ Q` and even
with `n : mynat`. Here the situation is different however. 
To prove `P ∨ Q` you need to give either a proof of `P` *or* a proof
of `Q`, so if `h : P ∨ Q` then `cases h with p q` will change one goal
into two, one with `p : P` and the other with `q : Q`. Similarly, each
natural is either `0` or `succ(d)` for `d` another natural, so if
`n : mynat` then `cases n with d` also turns one goal into two,
one with `n = 0` and the other with `d : mynat` and `n = succ(d)`.
-/


/- Tactic : left and right

## Summary

`left` and `right` work on the goal, and they change
`⊢ P ∨ Q` to `⊢ P` and `⊢ Q` respectively.

## Details

The tactics `left` and `right` work on a goal which is a type with
two constructors, the classic example being `P ∨ Q`. 
To prove `P ∨ Q` it suffices to either prove `P` or prove `Q`,
and once you know which one you are going for you can change
the goal with `left` or `right` to the appropriate choice.
-/

/- Tactic : exact

## Summary 

If the goal is `⊢ X` then `exact x` will close the goal if
and only if `x` is a term of type `X`. 

## Details

Say $P$, $Q$ and $R$ are types (i.e., what a mathematician
might think of as either sets or propositions),
and the local context looks like this: 

```
p : P,
h : P → Q,
j : Q → R
⊢ R
```

If you can spot how to make a term of type `R`, then you
can just make it and say you're done using the `exact` tactic
together with the formula you have spotted. For example the
above goal could be solved with

`exact j(h(p)),`

because $j(h(p))$ is easily checked to be a term of type $R$
(i.e., an element of the set $R$, or a proof of the proposition $R$).

-/

/- Tactic : apply

## Summary

If `h : P → Q` is a hypothesis, and the goal is `⊢ Q` then
`apply h` changes the goal to `⊢ P`. 

## Details

If you have a function `h : P → Q` and your goal is `⊢ Q`
then `apply h` changes the goal to `⊢ P`. The logic is
simple: if you are trying to create a term of type `Q`,
but `h` is a function which turns terms of type `P` into
terms of type `Q`, then it will suffice to construct a
term of type `P`. A mathematician might say: "we need
to construct an element of $Q$, but we have a function $h:P\to Q$
so it suffices to construct an element of $P$". Or alternatively
"we need to prove $Q$, but we have a proof $h$ that $P\implies Q$
so it suffices to prove $P$".

-/

/- Tactic : rw

## Summary

If `h` is a proof of `X = Y`, then `rw h,` will change
all `X`s in the goal to `Y`s. Variants: `rw ← h` (changes
`Y` to `X`) and
`rw h at h2` (changes `X` to `Y` in hypothesis `h2` instead
of the goal).

## Details

The `rw` tactic is a way to do "substituting in". There
are two distinct situations where use this tactics.

1) If `h : A = B` is a hypothesis (i.e., a proof of `A = B`)
in your local context (the box in the top right)
and if your goal contains one or more `A`s, then `rw h`
will change them all to `B`'s. 

2) The `rw` tactic will also work with proofs of theorems
which are equalities (look for them in the drop down
menu on the left, within Theorem Statements).
For example, in world 1 level 4
we learn about `add_zero x : x + 0 = x`, and `rw add_zero`
will change `x + 0` into `x` in your goal (or fail with
an error if Lean cannot find `x + 0` in the goal).

Important note: if `h` is not a proof of the form `A = B`
or `A ↔ B` (for example if `h` is a function, an implication,
or perhaps even a proposition itself rather than its proof),
then `rw` is not the tactic you want to use. For example,
`rw (P = Q)` is never correct: `P = Q` is the true-false
statement itself, not the proof.
If `h : P = Q` is its proof, then `rw h` will work.

Pro tip 1: If `h : A = B` and you want to change
`B`s to `A`s instead, try `rw ←h` (get the arrow with `\l` and
note that this is a small letter L, not a number 1).

### Example:
If it looks like this in the top right hand box:
```
x y : mynat
h : x = y + y
⊢ succ (x + 0) = succ (y + y)
```

then

`rw add_zero,`

will change the goal into `⊢ succ x = succ (y + y)`, and then

`rw h,`

will change the goal into `⊢ succ (y + y) = succ (y + y)`, which
can be solved with `refl,`.

### Example: 
You can use `rw` to change a hypothesis as well. 
For example, if your local context looks like this:
```
x y : mynat
h1 : x = y + 3
h2 : 2 * y = x
⊢ y = 3
```
then `rw h1 at h2` will turn `h2` into `h2 : 2 * y = y + 3`.
-/

/- Tactic : split

## Summary:

If the goal is `P ∧ Q` or `P ↔ Q` then `split` will break it into two goals.

## Details

If `P Q : Prop` and the goal is `⊢ P ∧ Q`, then `split` will change it into
two goals, namely `⊢ P` and `⊢ Q`. 

If `P Q : Prop` and the goal is `⊢ P ↔ Q`, then `split` will change it into
two goals, namely `⊢ P → Q` and `⊢ Q → P`.  

## Example:

If your local context (the top right window) looks like this
```
a b : mynat,
⊢ a = b ↔ a + 3 = b + 3
```

then after

`split,`

it will look like this:

```
2 goals
a b : mynat
⊢ a = b → a + 3 = b + 3

a b : mynat
⊢ a + 3 = b + 3 → a = b

-/

/- Tactic : intro

## Summary:

`intro p` will turn a goal `⊢ P → Q` into a hypothesis `p : P`
and goal `⊢ Q`. If `P` and `Q` are sets `intro p` means "let $p$ be an arbitrary element of $P$".
If `P` and `Q` are propositions then `intro p` says "assume $P$ is true". 

## Details

If your goal is a function or an implication `⊢ P → Q` then `intro`
will always make progress. `intro p` turns

`⊢ P → Q`

into 

```
p : P
⊢ Q
```

The opposite tactic to intro is `revert`; given the situation
just above, `revert p` turns the goal back into `⊢ P → Q`.

There are two points of view with `intro` -- the
function point of view (Function World) and the proposition
point of view (Proposition World).

## Example (functions)

What does it mean to define
a function? Given an arbitrary term of type `P` (or an element
of the set `P` if you think set-theoretically) you need
to come up with a term of type `Q`, so your first step is
to choose `p`, an arbitary element of `P`. 

`intro p,` is Lean's way of saying "let $p\in P$ be arbitrary".
The tactic `intro p` changes

```
⊢ P → Q
```

into

```
p : P
⊢ Q
```

So `p` is an arbitrary element of `P` about which nothing is known,
and our task is to come up with an element of `Q` (which can of
course depend on `p`).

## Example (propositions)

If your goal is an implication $P\implies Q$ then Lean writes
this as `⊢ P → Q`, and `intro p,` can be thought of as meaning
"let $p$ be a proof of $P$", or more informally "let's assume that
$P$ is true". The goal changes to `⊢ Q` and the hypothesis `p : P`
appears in the local context.
-/


/-
# Chapter 1 : Max

## Level 1

In this chapter we develop a basic interface for the `max a b` and `abs a`
function on the real numbers. Before we start, you will need to know
the basic API for `≤` and `<`, which looks like this:

```
example : a ≤ a := le_refl a

example : a ≤ b → b ≤ c → a ≤ c := le_trans

example : a ≤ b → b ≤ a → a = b := le_antisymm

example : a ≤ b ∨ b ≤ a := le_total a b

example : a < b ↔ a ≤ b ∧ a ≠ b := lt_iff_le_and_ne

example : a ≤ b → b < c → a < c := lt_of_le_of_lt

example : a < b → b ≤ c → a < c := lt_of_lt_of_le
```
-/

/- Axiom : le_refl a : a ≤ a
-/

/- Axiom : le_trans : a ≤ b → b ≤ c → a ≤ c
-/

/- Axiom : le_antisymm : a ≤ b → b ≤ a → a = b
-/

/- Axiom : le_total a b : a ≤ b ∨ b ≤ a
-/

/- Axiom : lt_iff_le_and_ne : a < b ↔ a ≤ b ∧ a ≠ b
-/

/- Axiom : lt_of_le_of_lt : a ≤ b → b < c → a < c 
-/

/- Axiom : lt_of_lt_of_le : a < b → b ≤ c → a < c
-/

/-
We start with `max a b := if a ≤ b then b else a`. It is
uniquely characterised by the following two properties, which are hence
all you will need to know:

```
theorem max_eq_right : a ≤ b → max a b = b

theorem max_eq_left : b ≤ a → max a b = a
```
-/

/- Axiom : max_eq_right : a ≤ b → max a b = b
-/

/- Axiom : max_eq_left : b ≤ a → max a b = a
-/

-- begin hide
def max (a b : ℝ) := if a ≤ b then b else a

-- need if_pos to do this one
theorem max_eq_right {a b : ℝ} (hab : a ≤ b) : max a b = b :=
begin
  unfold max,
  rw if_pos hab,  
end

-- need if_neg to do this one
theorem max_eq_left {a b : ℝ} (hba : b ≤ a) : max a b = a :=
begin
  by_cases hab : a ≤ b,
  { rw max_eq_right hab,
    exact le_antisymm hba hab,
  },
  { unfold max,
    rw if_neg hab,
  }
end
-- end hide

/-
All of these theorems are in the theorem statement box on the left.
See if you can now prove the useful `max_choice` lemma using them.
-/

/- Hint : Hint
Do a case split with `cases le_total a b`. 
-/

/- Lemma
For any two real numbers $a$ and $b$, either $\max(a,b) = a$
or $\max(a,b) = b$.
-/
theorem max_choice (a b : ℝ) : max a b = a ∨ max a b = b :=
begin
  cases le_total a b with hab hba,
  { right,
    exact max_eq_right hab
  },
  { left,
    exact max_eq_left hba
  }



end

end xena --hide
