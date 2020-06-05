import data.real.basic
import data.set.lattice
import topology.basic
import game.topology.union_closed_sets

open set

--begin hide
namespace xena
-- Work in progress
-- end hide


-- begin hide
-- Checking mathlib definitions
variable β : Type*
-- end hide

/- Lemma
Arbitrary intersection of closed sets is closed -- WIP, to do.
-/
lemma is_closed_inter_of_closed (X : β → set ℝ ) ( hj : ∀ j, is_closed (X j) )
    : is_closed (Inter X) :=
begin
    sorry,
end

end xena -- hide
