--import algebra.pointwise tactic

/-
The below is not actually needed for this project
/-- Makes an add_comm_monoid in Lean's sense from a more minimal
set of axioms, deducing zero_add from add_comm and add_zero
-/
def add_comm_monoid.mk' {M : Type*} [has_add M] [has_zero M] 
(add_assoc : ∀ a b c : M, a + b + c = a + (b + c))
(add_zero : ∀ a : M, a + 0 = a)
(add_comm : ∀ a b : M, a + b = b + a) :
add_comm_monoid M :=
{ add := (+),
  add_assoc := add_assoc,
  zero := (0),
  add_zero := add_zero,
  add_comm := add_comm,
  zero_add := λ a, add_comm a 0 ▸ add_zero a,
}

-- #check add_comm_monoid.mk
-/