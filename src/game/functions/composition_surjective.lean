import data.real.basic
open function

/-
# Chapter 6 : Functions

## Level 6

A classical result in composition of functions.
Now going the other way around.
-/

/- Lemma
If composition of $f$ and $g$ is surjective, then $g$ is injective.
-/
theorem composition_surjective 
    (X Y Z : set ℝ) (f : X → Y) (g : Y → Z) : surjective (g ∘ f) → surjective g :=
begin
    intros sgf z,
    have hx := sgf z,
    cases hx with x gfxz,
    use f x,
    exact gfxz, done
end

