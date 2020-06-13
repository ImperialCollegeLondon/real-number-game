import data.real.basic
import topology.basic
open function
open set

namespace xena -- hide

/-
# Chapter 7 : Cardinality

## Level 3

A classical result about countable sets.
-/

/- Lemma
If $f : X \to Y$ is an injective function and $Y$ is countable, then
$X$ is also countable.
-/
theorem countable_inj (X Y : set ℝ) (f : X → Y) (hY : countable Y) : 
    injective f → countable X :=
begin
   intro hf,
    have H := countable_iff_exists_injective.1 hY,
    cases H with g hg,
    have G := countable_iff_exists_injective.2 ⟨g ∘ f, injective.comp hg hf⟩,
    exact G, done
end

end xena -- hide

-- begin hide
-- term mode proof due to Kenny Lau
theorem countable_inj_2 (X Y : set ℝ) (f : X → Y) (hY : countable Y) :
    injective f → countable X :=
λ hf, let ⟨g, hg⟩ := countable_iff_exists_injective.1 hY in
countable_iff_exists_injective.2 ⟨g ∘ f, injective.comp hg hf⟩
-- end hide
