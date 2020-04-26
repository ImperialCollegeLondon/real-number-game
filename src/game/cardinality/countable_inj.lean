import data.real.basic
import topology.basic
open function
open set

/-
# Chapter 7 : Cardinality

## Level 2

A classical result about countable sets.
-/

/- Lemma
If $f : X \to Y$ is an injective function and $Y$ is countable, then
$X$ is also countable.
-/
theorem countable_inj (X Y : set ℝ) (f : X → Y) (hY : countable Y) : 
    injective f → countable X :=
begin
   sorry,
end