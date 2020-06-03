import tactic

open_locale classical

open set

namespace rng

variables {X : Type} (a : X) {x : X} {A B : set X}

/-- Humans want these -/
lemma mem_univ (a : X) : a ∈ (univ : set X) := mem_univ a
lemma not_mem_empty (a : X) : ¬ (a ∈ (∅ : set X)) := not_false
lemma mem_set_iff (a : X) (P : X → Prop) : a ∈ {b : X | P b} ↔ P a := iff.rfl

/-- Humans want these -/
lemma mem_union_iff : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := iff.rfl 
lemma mem_inter_iff : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B := iff.rfl
lemma eq_iff : A = B ↔ ∀ x : X, x ∈ A ↔ x ∈ B := ext_iff
lemma subset_iff : A ⊆ B ↔ ∀ x : X, x ∈ A → x ∈ B := iff_of_eq subset_def --iff.rfl avoids eq.rec
-- call it subset_iff?

variables (ι : Type) (f : ι → set X)

/-- Humans want these -/
lemma mem_Union_iff : (x ∈ ⋃(i : ι), f i) ↔ ∃ (i : ι), x ∈ f i := mem_Union
lemma mem_Inter_iff : (x ∈ ⋂(i : ι), f i) ↔ ∀ (i : ι), x ∈ f i := mem_Inter

end rng
