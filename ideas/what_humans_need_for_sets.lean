import tactic

open_locale classical

variables (X : Type) (x : X) (A B : set X)

open set

/-- Humans want these -/
example (a : X) : a ∈ (univ : set X) := mem_univ a
example (a : X) : ¬ (a ∈ (∅ : set X)) := not_false
example (a : X) (P : X → Prop) : a ∈ {b : X | P b} ↔ P a := iff.rfl

/-- Humans want these -/
example : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := iff.rfl -- let's call it mem_union_iff
example : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B := iff.rfl -- let's called it mem_inter_iff
example : A = B ↔ ∀ x : X, x ∈ A ↔ x ∈ B := ext_iff
example : A ⊆ B ↔ ∀ x : X, x ∈ A → x ∈ B := iff_of_eq subset_def --iff.rfl avoids eq.rec
-- call it subset_iff?

variables (ι : Type) (f : ι → set X)

/-- Humans want these -/
example (a : X) : (a ∈ ⋃(i : ι), f i) ↔ ∃ (i : ι), a ∈ f i := mem_Union
example (a : X) : (a ∈ ⋂(i : ι), f i) ↔ ∀ (i : ι), a ∈ f i := mem_Inter

