import data.real.basic
import data.set.lattice

open set

--begin hide
namespace xena
-- This will eventually be the first level, containing basic definitions
-- Work in progress
-- First I used ⊂ in the definition, then changed to ⊆ 
-- in order to be able to use subset.trans -- DS
-- end hide

def is_open (X : set ℝ) := ∀ x ∈ X, ∃ δ > 0, { y : ℝ  | x - δ < y ∧ y < x + δ } ⊆ X
variable β : Type

-- begin hide
-- Checking definitions
def countable_union (X : nat → set ℝ) := {t : ℝ | exists i, t ∈ X i}
-- end hide

/- Lemma
Arbitrary union of open sets is open -- WIP, to do.
-/
lemma is_open_union_of_open (X : β → set ℝ ) ( hj : ∀ j, is_open (X j) )
    : is_open (Union X) :=
begin
    intros x hx,
    simp at hx,
    cases hx with i hi,
    have H := hj i,
    have G := H x hi,
    cases G with d hd, use d,
    cases hd with hd1 hd2,
    split, exact hd1,
    have hd3 : X i ⊆ Union X, 
        intros t ht, simp,
        use i, exact ht,
    exact subset.trans hd2 hd3, done
end


end xena -- hide