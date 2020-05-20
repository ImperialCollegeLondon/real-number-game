import data.real.basic
import data.set.lattice
import topology.basic
import game.topology.union_open_sets

open set

--begin hide
namespace xena
-- This will eventually be the first level, containing basic definitions
-- Work in progress
-- end hide


-- begin hide
-- Checking mathlib definitions
variable β : Type
variable fβ : finset β
--variable s : set β 
-- end hide

/- Lemma
Finite intersection of open sets is open -- WIP, to do.
-/
lemma is_open_fin_inter_of_open (s : set β) (hs : finite s) (X : s → set ℝ ) 
    ( hj : ∀ j, is_open (X j) )
-- needed to make this finite; used finite s, but X should be X : β → set ℝ 
    : is_open (Inter X) :=
begin
    sorry,
end

end xena -- hide