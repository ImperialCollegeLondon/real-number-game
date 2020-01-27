-- list of functions which will surely be useful

import data.real.basic

-- in order.bounds 

#check @upper_bounds -- and lower_bounds 
-- upper_bounds : Π {α : Type u_1} [_inst_1 : preorder α], set α → set α
#check @is_least -- and is_greatest
-- is_least : Π {α : Type u_1} [_inst_1 : preorder α], set α → α → Prop
#check @is_lub -- and is_glb
-- is_lub : Π {α : Type u_1} [_inst_1 : preorder α], set α → α → Prop

-- and lots of lemmas e.g. eq_of_is_lub_of_is_lub

-- in order.conditionally_complete_lattice

#check @bdd_above -- "is bounded above" -- and bdd_below
-- bdd_above : Π {α : Type u_1} [_inst_1 : preorder α], set α → Prop 



-- in order.complete_lattice -- notation \Lub = ⨆ 
#check @lattice.supr -- sup over an indexed family of elements
-- lattice.supr : Π {α : Type u_1} {ι : Sort u_2} [_inst_1 : lattice.has_Sup α], (ι → α) → α

-- see also lattice.infi = ⨅ = \Glb

-- in data.real.basic
#check real.Sup 
-- real.Sup : set ℝ → ℝ

#check real.Sup_le
/-
real.Sup_le :
  ∀ (S : set ℝ),
    (∃ (x : ℝ), x ∈ S) →
    (∃ (x : ℝ), ∀ (y : ℝ), y ∈ S → y ≤ x) →
    ∀ {y : ℝ}, real.Sup S ≤ y ↔ ∀ (z : ℝ), z ∈ S → z ≤ y
-/