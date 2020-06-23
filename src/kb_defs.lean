import tactic

open_locale classical

open set

namespace xena

variables {X : Type} (a : X) {x : X} {A B : set X}

/-- Humans want these in levels 1-6 -/
lemma mem_union_iff : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := iff.rfl 
lemma mem_inter_iff : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B := iff.rfl
lemma mem_sdiff_iff : x ∈ A \ B ↔ x ∈ A ∧ x ∉ B := iff.rfl
lemma mem_neg_iff : x ∈ -A ↔ x ∉ A := iff.rfl

lemma ext_iff : A = B ↔ ∀ x : X, x ∈ A ↔ x ∈ B := ext_iff
lemma subset_iff : A ⊆ B ↔ ∀ x : X, x ∈ A → x ∈ B := iff.rfl

/-- Humans want these in level 7 -/
--lemma mem_univ (a : X) : a ∈ (univ : set X) := mem_univ a
lemma mem_empty_iff (a : X) : a ∈ (∅ : set X) ↔ false := iff.rfl 
--lemma not_mem_empty (a : X) : ¬ (a ∈ (∅ : set X)) := not_false
--lemma mem_set_iff (a : X) (P : X → Prop) : a ∈ {b : X | P b} ↔ P a := iff.rfl




variables (ι : Type) (f : ι → set X)

/-- Humans might want these but we don't use them yet -/
lemma mem_Union_iff : (x ∈ ⋃(i : ι), f i) ↔ ∃ (i : ι), x ∈ f i := mem_Union
lemma mem_Inter_iff : (x ∈ ⋂(i : ι), f i) ↔ ∀ (i : ι), x ∈ f i := mem_Inter

end xena
