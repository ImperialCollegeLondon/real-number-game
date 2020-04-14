import data.real.basic
open function


/- Lemma
If $f : X \to Y$ and $g : Y \to Z$ are both injective functions, then
the function resulting from their composition is also injective.
-/
theorem both_injective 
    (X Y Z : set ℝ) (f : X → Y) (g : Y → Z) : injective f ∧ injective g → injective (g ∘ f) :=
begin
    intros h a b ha,
    apply h.left,
    apply h.right, 
    --either this: assumption, --or the line below
    exact ha, done
end
