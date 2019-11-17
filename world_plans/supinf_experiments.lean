import data.real.basic -- Lean has a good API for reals so I'm happy to use them.
import algebra.pointwise -- for addition on set ℝ
import for_mathlib.add_comm_monoid
local attribute [instance] set.add_comm_monoid

/-
Goal : prove the following theorem.

Sup(X+Y)=Sup(X)+Sup(Y).
Goal after that: state and prove Richard Thomas' problem sheet question. 
-/

/-- This should be part of a controlled natural language, not a Lean definition -/
class bounded_above (X : set ℝ) : Prop := 
(is_bounded_above : bounded (≤) X)

local attribute [instance] set.add_comm_monoid

instance (X Y : Type*) : nonempty X → nonempty Y → nonempty (X × Y)
| ⟨x⟩ ⟨y⟩ := ⟨(x, y)⟩

--set_option pp.notation false
#check ∀ (X : Type) (P : X → Prop), {x : X | P x}
/-- version of set_of without universes and {}s -/
def set_of' (X : Type) (P : X → Prop) := {x : X | P x}
#check set_of'
#print set_of'
/-- version of subtype without universes and {} -/
def subtype' (X : Type) (P : X → Prop) := {x : X // P x}
#check subtype'
#check set_of'
#check @set_of
example : set_of' = @set_of := rfl
#check subtype'
-- question: relationship between subtype' and set_of'
--set_option pp.notation false
#check set_of'
#print set_of
#check subtype'
#print subtype
/-
/- Remark: subtype must take a Sort instead of Type because of the axiom strong_indefinite_description. -/
structure subtype {α : Sort u} (p : α → Prop) :=
(val : α) (property : p val)
-/
#print set_of
variables (R : Type) (P : R → Prop)
#check (@subtype.val R P : subtype P → R)
#check (@subtype.property R P : ∀ (c : subtype P), P (c.val))
#check set_of' R P
-- set_of must be notation.
example : set_of' R P = P := rfl
#check subtype' R P
#print prefix subtype

def subtype'.val : subtype P → R := subtype.val
def subtype'.property : ∀ (c : subtype P), P (c.val) := subtype.property

#check @coe_sort
#check has_coe_to_sort

example : @id _ = @set_of R := rfl -- set_of is the identity function
example : set_of' R = id := rfl
example : set R ≃ (R → Prop) := {
  to_fun := id,
  inv_fun := set_of, -- id also works
  left_inv := λ _, rfl,
  right_inv := λ _, rfl }

#check subtype' R
theorem real.add_nonempty (X Y : set ℝ) :
  nonempty X → nonempty Y → nonempty (subtype' ℝ ((X + Y) : set ℝ))
| ⟨x⟩ ⟨y⟩ := ⟨⟨x.val + y.val, ⟨x.val, x.property, y.val, y.2, rfl⟩⟩⟩

--set_option pp.notation false
-- coe_sort is ↥
#check real.add_nonempty
#print has_coe_to_sort
/-
class has_coe_to_sort (a : Sort u) : Type (max u (v+1)) :=
(S : Sort v) (coe : a → S)
-/
example : has_coe_to_sort (set ℝ) := by apply_instance -- set.has_coe_to_sort
#print set.has_coe_to_sort
#check set.has_coe_to_sort.coe -- : set X → has_coe_to_sort.S (set X)
#check set.has_coe_to_sort.S --: set ℝ → Type
#check (subtype' ℝ : (ℝ → Prop) → Type)
example : subtype' R P = set.has_coe_to_sort.S := sorry
--#check @coe_sort : 
#exit

theorem real.Sup_add -- or is it real.Sup.add?
  (X : set ℝ) (h1X : nonempty X) (h2X : bounded_above X)
  (Y : set ℝ) (h1Y : nonempty Y) (h2Y : bounded_above Y) : 
  real.Sup {z : ℝ | ∃ (x ∈ X) (y ∈ Y), z = x + y} = real.Sup X + real.Sup Y  :=
begin
  
  apply le_antisymm,
  { rw real.Sup_le,
    sorry
  },
  {
    sorry
  }
end

/-
Question: should there be an "add top and bottom" type?
Question: should instance : has_add (set ℝ) exist?

-/

/-
/-- It's zero if the sup doesn't exist -/
def Sup (S : set ℝ) : ℝ

theorem Sup_le (S : set ℝ) (h₁ : ∃ x, x ∈ S) (h₂ : ∃ x, ∀ y ∈ S, y ≤ x)
  {y} : Sup S ≤ y ↔ ∀ z ∈ S, z ≤ y

theorem lt_Sup (S : set ℝ) (h₁ : ∃ x, x ∈ S) (h₂ : ∃ x, ∀ y ∈ S, y ≤ x)
  {y} : y < Sup S ↔ ∃ z ∈ S, y < z

theorem le_Sup (S : set ℝ) (h₂ : ∃ x, ∀ y ∈ S, y ≤ x) {x} (xS : x ∈ S) : x ≤ Sup S

theorem Sup_le_ub (S : set ℝ) (h₁ : ∃ x, x ∈ S) {ub} (h₂ : ∀ y ∈ S, y ≤ ub) : Sup S ≤ ub

lemma is_lub_Sup {s : set ℝ} {a b : ℝ} (ha : a ∈ s) (hb : b ∈ upper_bounds s) :
  is_lub s (Sup s) :=
-/

/-- The type $$[-∞,+∞]$$ -/
def ereal : Type := with_bot (with_top ℝ)

--def is_ub (X : set ℝ) (b : ℝ) := ∀ x ∈ X, x ≤ b
--def is_lub (X : set ℝ) (l : ℝ) := is_ub X l ∧  

/-
theorem exists_sup (S : set ℝ) : (∃ x, x ∈ S) → (∃ x, ∀ y ∈ S, y ≤ x) →
  ∃ x, ∀ y, x ≤ y ↔ ∀ z ∈ S, z ≤ y
-/