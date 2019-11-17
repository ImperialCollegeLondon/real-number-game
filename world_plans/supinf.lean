import data.real.basic -- Lean has a good API for reals so I'm happy to use them.
import algebra.pointwise -- for addition on set ℝ
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

--set_option pp.all true
theorem real.add_nonempty (X Y : set ℝ) :
  nonempty X → nonempty Y → nonempty (subtype (X + Y : set ℝ))
| ⟨x⟩ ⟨y⟩ := ⟨⟨x.val + y.val, ⟨x.val, x.property, y.val, y.2, rfl⟩⟩⟩

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