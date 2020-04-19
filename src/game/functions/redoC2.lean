import data.real.basic

open function

-- Now go the other way around
theorem composition_injective 
    (X Y Z : Type u) (f : X → Y) (g : Y → Z) : injective (g ∘ f) → injective f :=
begin
    intros h a b ha,
    have applyg : g (f a) = g (f a), refl,
    rw ha at applyg {occs := occurrences.pos [2]},
    apply h,
    exact applyg, done 
end

theorem composition_surjective 
    (X Y Z : Type u) (f : X → Y) (g : Y → Z) : surjective (g ∘ f) → surjective g :=
begin
    intros sgf z,
    have hx := sgf z,
    cases hx with x gfxz,
    use f x,
    exact gfxz, done
end

