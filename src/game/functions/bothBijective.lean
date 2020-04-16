import data.real.basic
open function


/- Lemma
If $f : X \to Y$ and $g : Y \to Z$ are both bijective functions, then
the function resulting from their composition is also bijective.
-/
theorem both_bijective
    (X Y Z : set ℝ) (f : X → Y) (g : Y → Z) : 
    bijective f ∧ bijective g → bijective (g ∘ f) :=
begin
    -- Since $f$ and $g$ are bijective, they are also both injective and surjective.
    rintro ⟨⟨hfi, hfs⟩, hgi, hgs⟩,
    split,
    -- Since $f$ and $g$ are injective, $g ∘ f$ is injective by a previous result.
    apply both_injective,
    split,
    repeat {assumption},
    -- Similarly, since $f$ and $g$ are surjective, $g ∘ f$ is surjective.
    apply both_surjective,
    split,
    -- Hence, since $g ∘ f$ is injective and surjective, $g ∘ f$ is bijective.
    repeat {assumption}, done
end

