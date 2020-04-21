import data.real.basic
open function

/-
# Chapter 6 : Functions

## Level 5

A classical result in composition of functions. Now going the other way around
-/


/- Lemma
If composition of $f$ and $g$ is injective, then $f$ is injective.
-/
theorem composition_injective 
    (X Y Z : set ℝ) (f : X → Y) (g : Y → Z) : injective (g ∘ f) → injective f :=
begin
    intros h a b ha,
    have applyg : g (f a) = g (f a), refl,
    rw ha at applyg {occs := occurrences.pos [2]},
    apply h,
    exact applyg, done 
end

