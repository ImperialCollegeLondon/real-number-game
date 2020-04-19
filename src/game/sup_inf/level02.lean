import data.real.basic

-- World name : Sup and Inf

/-
# Chapter 2 : Sup and Inf

# Level 2 : Any non-empty, bounded set of reals has a supremum.
-/

definition is_upper_bound (S : set ℝ) (x : ℝ) := x ∈ upper_bounds S 
definition has_lub (S : set ℝ) := ∃ x, is_lub S x 
local attribute [instance] classical.prop_decidable --hide


/- Lemma
Any non-empty and bounded set of reals has a supremum.
-/
theorem nonempty_and_bounded_of_has_LUB (S : set ℝ) (H : has_lub S) : 
  (S ≠ ∅) ∧ (∃ x, is_upper_bound S x) :=
begin
  cases H with b Hb,
  -- b is LUB, Hb is proof it's LUB
  split,
  { -- first prove S is not empty, by contradiction as usual with empty sets
    intro Hempty,
    have H1 : (b-1) ∈ upper_bounds S,
      change ∀ x ∈ S, x ≤ (b-1),
      by_contradiction hn,
      push_neg at hn,
      cases hn with x h1, 
      cases h1 with h11 h12,
      rw Hempty at h11, 
      exact h11, 
    have HH := Hb.2 H1, -- b - 1 is an upper bound
    linarith,
  },
  {
     existsi b,
     exact Hb.1,
  }, 
  done
end 