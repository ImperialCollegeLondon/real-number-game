import data.real.basic
import topology.basic
open function
open set

/-
# Chapter 7 : Cardinality

## Level 1

A classical result about finite sets.
-/

-- begin hide
local attribute [instance] classical.prop_decidable
-- end hide

/- Lemma
If $f : X \to Y$ is an injective function and $Y$ is finite, then
$X$ is also finite.
-/
theorem finite_inj (X Y : set ℝ) (f : X → Y) (hY : finite Y) : 
    injective f → finite X :=
begin
   sorry,
end
