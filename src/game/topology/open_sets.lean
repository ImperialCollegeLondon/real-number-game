import data.real.basic
import topology.basic

--begin hide
namespace xena
-- This will eventually be the first level, containing basic definitions
-- Work in progress
-- end hide

def is_open (X : set ℝ) := ∀ x ∈ X, ∃ δ > 0, { y : ℝ  | x - δ < y ∧ y < x + δ } ⊂ X
def countable_union (X : nat → set ℝ) := {t : ℝ | exists i, t ∈ X i}
def open_sets (n : ℕ) : set ℝ := {x | ↑n < x ∧ x < (n+1)}  -- needs generalization

/- Lemma
A countable union of open sets is open.
Arbitrary unions -- WIP, to do.
-/
lemma countable_union_open_sets : is_open (countable_union open_sets) :=
begin
    sorry,
end



end xena -- hide