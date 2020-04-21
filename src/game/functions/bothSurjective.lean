import data.real.basic
open function

/-
# Chapter 6 : Functions

## Level 2

A classical result in composition of functions.
-/

/- Lemma
If $f : X \to Y$ and $g : Y \to Z$ are both surjective functions, then
the function resulting from their composition is also surjective.
-/
theorem both_surjective
    (X Y Z : set ℝ) (f : X → Y) (g : Y → Z) : 
    surjective f ∧ surjective g → surjective (g ∘ f) :=
begin
    intros H z,
    cases H with sf sg,
    have hy : ∃ y : Y, g y = z, from sg z,
    cases hy with y gy,
    have hx : ∃ x : X, f x = y, from sf y,
    cases hx with x fx,
    use x, rw ← gy, rw ← fx, done
end
