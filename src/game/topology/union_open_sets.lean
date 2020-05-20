import data.real.basic
import data.set.lattice

open set

--begin hide
namespace xena
-- This will eventually be the first level, containing basic definitions
-- Work in progress
-- end hide

def is_open (X : set ℝ) := ∀ x ∈ X, ∃ δ > 0, { y : ℝ  | x - δ < y ∧ y < x + δ } ⊂ X
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
    sorry,
end


end xena -- hide