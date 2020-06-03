import game.sets.sets_level04 -- hide

namespace xena -- hide

variable X : Type --hide

/-
# Chapter 1 : Sets

## Level 5
-/


/-
You should now be able to prove the theorem below if you
use `split` and `cases` together with `set.subset.antisymm`.
-/

/- Lemma
If $A$ and $B$ are sets of any type $X$, then
$$ A \subseteq B \iff A \cap B = A.$$
-/

set_option trace.simplify.rewrite true
--set_option trace.rewrite.simplify true
theorem subset_iff_intersection_eq (A : set X) (B : set X) : A ⊆ B ↔ A ∩ B = A := 
begin
  rw subset_iff,
  rw eq_iff,
  split,
  { intros h x,
    specialize h x,
    rw mem_inter_iff,
    tauto!
  },
  { intros h x hx,
    specialize h x,
    rw mem_inter_iff at h,
    tauto!,
  }
end

theorem subset_iff_intersection_eq' (A : set X) (B : set X) : A ⊆ B ↔ A ∩ B = A := 
begin
  rw subset_iff,
  rw eq_iff,
  apply forall_congr, -- clever trick
  intro x,
  rw mem_inter_iff, -- no longer under a binder
  tauto!
end


-- begin
--     split,
--     intro H, apply set.subset.antisymm,
--     intros x hx, cases hx with hA hB, exact hA,
--     intros x hx, split, exact hx, exact H hx,
--     intro H, intros x hx, 
--     have G : x ∈ A ∩ B, rw H, exact hx,
--     cases G with hA hB, exact hB, done
-- end

end xena -- hide