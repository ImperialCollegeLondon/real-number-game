import algebra.pointwise

-- being PR'ed 1696 or something, ready to merge, will error later
namespace set
variable (α : Type*)
def comm_monoid [comm_monoid α] : comm_monoid (set α) :=
@comm_semiring.to_comm_monoid (set α) pointwise_mul_comm_semiring

def add_comm_monoid [add_comm_monoid α] : add_comm_monoid (set α) :=
show @add_comm_monoid (additive (set (multiplicative α))),
from @additive.add_comm_monoid _ (set.comm_monoid (multiplicative α))

attribute [to_additive set.add_comm_monoid] set.comm_monoid
end set
-- end of PR 

-- to mathlib?
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

-- apparently not to mathlib?
local attribute [instance] set.add_comm_monoid
