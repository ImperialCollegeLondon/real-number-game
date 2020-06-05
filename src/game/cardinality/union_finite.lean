import data.real.basic
import topology.basic
open function
open set

namespace xena -- hide

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
theorem union_finite (X Y : set ℝ) : finite X → finite Y → finite (X ∪ Y)  :=
begin
    sorry,
end

end xena -- hide
