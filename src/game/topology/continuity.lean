import data.real.basic
import topology.basic

namespace xena -- hide

open function
open real
open set

/-
Classic eps-delta definition of continuity equivalent to topological definition.

Work in progress.
-/

notation `|` x `|` := abs x

def continuous_at_x (f : ℝ → ℝ) (x : ℝ) := 
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, |x - y| < δ → |f x - f y| < ε
def continuous_on_set (f : ℝ → ℝ) (X : set ℝ) :=
    ∀ x ∈ X, continuous_at_x f x
def open_in_R (Y : set ℝ) := ∀ x ∈ Y, ∃ ε : ℝ, 0 < ε ∧ { y | |x-y| < ε } ⊂ Y
def open_in_X (S : set ℝ) (X : set ℝ) (hS : S ⊂ X) := ∃ Y : set ℝ, 
    S = Y ∩ X ∧ open_in_R Y 
def preimage_in_X (f : ℝ → ℝ) (X : set ℝ) (T : set ℝ) :=
    { x | x ∈ X ∧ ∃ t ∈ T, f x = t}
def continuous_on_topo_def (f : ℝ → ℝ) (X : set ℝ) :=
    ∀ T : set ℝ, open_in_R T → open_in_R (preimage_in_X f X T)


/-
theorem continuous_on_topo_def2 (f : ℝ → ℝ) (X : set ℝ) :
  ∀ x ∈ X, ∀ t : set ℝ, is_open t → f x ∈ t → ∃ u, is_open u ∧ x ∈ u ∧
    u ∩ X ⊆ f ⁻¹' t :=
-/


/- Lemma
Equivalent definitions of continuity.
-/
lemma continuity_topological (f : ℝ → ℝ) (X : set ℝ) :
    continuous_on_set f X ↔ continuous_on_topo_def f X :=
begin
    sorry,
end

end xena


