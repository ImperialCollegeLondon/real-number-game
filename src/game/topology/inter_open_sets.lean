import data.real.basic
import data.set.lattice
import topology.basic
import game.topology.union_open_sets

open set

--begin hide
namespace xena
-- Work in progress
-- end hide


-- begin hide
-- Checking mathlib definitions
variable β : Type*
variable [fintype β]
-- end hide

/- Lemma
Finite intersection of open sets is open -- WIP, to do.
-/
lemma is_open_fin_inter_of_open (X : β → set ℝ ) ( hj : ∀ j, is_open (X j) )
    : is_open (Inter X) :=
begin
    sorry,
end

end xena -- hide
