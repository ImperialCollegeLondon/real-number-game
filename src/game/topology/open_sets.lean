import data.real.basic
import topology.basic
import data.set.lattice

--begin hide
namespace xena
-- This will eventually be the first level, containing basic definitions
-- Work in progress
-- end hide

def is_open (X : set ℝ) := ∀ x ∈ X, ∃ δ > 0, { y : ℝ  | x - δ < y ∧ y < x + δ } ⊂ X

-- begin hide
-- Checking mathlib definitions
def countable_union (X : nat → set ℝ) := {t : ℝ | exists i, t ∈ X i}
def open_sets (n : ℕ) : set ℝ := {x | ↑n < x ∧ x < (n+1)}  -- needs generalization
open set
#check Union
def I := set (set ℝ)
variable J : set (set ℝ)
variable f : I → set ℝ 
#check Union f
variable β : Type
variable K : set β
#check K
lemma arbitrary_union_open_sets_v1 (J : set β ) (f : J → set ℝ ) ( hj : ∀ j : J, is_open (f j) )
-- I'd rather write `hj : ∀ j ∈ J`, but not sure how to handle that `has_mem` yet
-- Is that possible? Is it desirable?
    : is_open (Union f) := sorry
lemma arbitrary_union_open_sets_v2 :
    ∀ J : set β,
    ∀ f : J → set ℝ,
    ∀ j, is_open (f j)  → is_open (Union f) := sorry
-- end hide

/- Lemma
Arbitrary union of open sets is open -- WIP, to do.
Could also make J simpler-looking, as above.
-/
lemma arbitrary_union_open_sets (J : set β) (f : J → set ℝ ) ( hj : ∀ j, is_open (f j) )
    : is_open (Union f) :=
begin
    sorry,
end


end xena -- hide