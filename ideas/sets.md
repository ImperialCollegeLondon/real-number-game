# How to teach a mathematician do do set theory in Lean

What does a mathematician think that a set *is*? What is the interface? If they're doing mathematics in set theory then they will think that the axioms of set theory are part of the interface. Let's go through the axioms.

## Extensionality

The statement

``A = B ↔ ∀ x : X, x ∈ A ↔ x ∈ B``

is "true by an axiom in set theory. It corresponds to the non-trival proof `set.ext_iff` in Lean

## Foundation

This is more a deficit of set theory than anything else; it is not used in generic mathematics. The drastic type theory version is the fact that distinct types are disjoint. There is no statement involving objects in `set X` which Foundation corresponds to.

## Separation

The fact that you can make the set ``{a : X | P a}`` is built into Lean's notation. It's a constructor for `set X`.

## Pairing and Infinity

Both of these are explaining how to make sets. Pairing is used to make the first set of size 1, and Infinity to make the first infinite set. These are all swallowed up into Lean's concept of an inductive type: `{a : X | a = r or a = s}` is built using the `or` inductive type, and the natural numbers are built using the `nat` inductive type. 

## The union axiom and the replacement axiom

The union of two sets (which you can build in ZFC using the pairing axiom and the union axiom) obeys the property

``x ∈ A ∪ B ↔ x ∈ A or x ∈ B``

. This is "true by an axiom". But this is actually the _definition_ of `A ∪ B`. Similarly the _definition_ of ``x ∈ A ∩ B`` is ``x ∈ A ∧ x ∈ B``. That's why you can be clever and `split` when faced with the goal ``x ∈ A ∩ B``

But the full union axiom in ZFC, and the part of the replacement axiom which is used in generic mathematics is

```
-- replacement and Union
variables (ι : Type) (f : ι → set X)

#check ⋃(i : ι), f i 

example (a : X) : (a ∈ ⋃(i : ι), f i) ↔ ∃ (i : ι), a ∈ f i :=
set.mem_Union
```

Note that the proof is not ``iff.rfl``, to my mild surprise. 

## The power set axiom

If `X` is a type, then `set X` is the type of subsets of `X`.

## The axiom of choice

This is essentially an axiom in Lean: we use `classical.choice` here.

```
variables (ι : Type) (f : ι → set X)

example : (∀ i, nonempty (f i)) → ∃ g : ι → X, ∀ i, g i ∈ f i :=
begin
  intro h,
  use λ i, (classical.choice (h i)).1,
  intro i,
  exact (classical.choice (h i)).2
end
```










`