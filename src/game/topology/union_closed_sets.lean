import data.real.basic
import data.set.lattice
import topology.basic
import game.topology.union_open_sets

open set

--begin hide
namespace xena
-- end hide

def is_closed (X : set ℝ) := is_open {x : ℝ | x ∉ X }

-- begin hide
-- Checking mathlib definitions
variable β : Type*  -- finite unions only
variable [fintype β]
-- end hide

/- Lemma
Finite union of closed sets is closed -- WIP, to do.
-/
lemma is_closed_fin_union_of_closed (X : β → set ℝ ) ( hj : ∀ j, is_closed (X j) )
    : is_closed (Union X) :=
begin
    sorry,
end


end xena -- hide