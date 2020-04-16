import data.real.basic
open function

-- inverses
def two_sided_inverse {X Y : Type u} (f : X → Y) (g : Y → X) 
:= (∀ x : X, (g ∘ f)(x) = x) ∧ (∀ y : Y, (f ∘ g)(y) = y)

/- Lemma
A function $f : X → Y$ has a two-sided inverse if and only if it is a bijection.
-/

theorem exist_two_sided_inverse (X Y : set ℝ) (f : X → Y) : 
    (∃ g : Y → X, two_sided_inverse f g) ↔ bijective f :=
begin
    split,
    {
        intro Eg,
        cases Eg with g invg,
        cases invg with gf fg,
        -- show f is injective
        have hinjf : injective f,
            intros x1 x2 f1f2,
            replace f1f2 : g ( f x1 ) = g ( f x2 ),
            rw f1f2,
            have h1 : g (f x1) = x1 := gf x1,
            have h2 : g (f x2) = x2 := gf x2,
            rw [ h1, h2 ] at f1f2, exact f1f2,
        -- show f is surjective 
        have hsurf : surjective f,
            intro y,
            existsi g y,
            exact fg y,
        -- put these results together
        exact and.intro hinjf hsurf,
    },
    {
        rintro bf,
        cases bf with finj fsurj,
        -- Since $f$ is surjective, $∀ y ∈ Y, ∃ x ∈ X$ such that $f(x) = y$; 
        -- choose this $x$ to be the output of $g(y)$.
        choose g hg using fsurj,
        existsi g,
        split,
        intro x,
        -- by definition of $g$, $∀ y ∈ Y, f(g(y)) = y$ 
        -- so we have $f(g(f(x))) = f(x)$:
        have hx : f (g (f x)) = f x, rw hg (f x),
        apply finj, 
        exact hx,
        exact hg,
    }
end

