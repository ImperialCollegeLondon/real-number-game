import data.real.basic

namespace xena -- hide

/-
# Chapter 3 : Sup and Inf

## Level 12
-/

def unboundedAbove (A : set ℝ) := ∀ x : ℝ, x > 0 → ∃ a ∈ A, x < a
-- Might want to make this into an axiom to be placed on the left
def archimPrinciple := ∀ x : ℝ, x > 0 →  ∃ n : ℕ, n > 0 ∧ (1/n : ℝ) < x 

/- Lemma
The Archimedean principle is equivalent to the set of natural numbers being unbounded above.
-/
lemma nats_unbounded_iff : 
    unboundedAbove {x : ℝ | ∃ n : ℕ, x = n ∧ n > 0} ↔ archimPrinciple :=
begin
    split,
    -- left-right implication
    intros unb x hx,
    set A := {x : ℝ | ∃ n : ℕ, x = n ∧ x > 0} with hA,
    have h1x : (1/x) > 0, from one_div_pos_of_pos hx,
    have h1 := unb (1/x) h1x,
    -- rcases h1 with ⟨nx, ⟨n, rfl⟩, h2⟩,
    cases h1 with nx hnx,
    cases hnx with h1 h2,
    cases h1 with xn h12,
    existsi xn, rw h12.left at h2, 
    have h0 : 0 < (1:ℝ), norm_num,
    have h3 := div_lt_div_of_pos_of_lt_of_pos h1x h2 h0,
    split, exact h12.right,
    simp at h3, simp, 
    exact h3,
    -- right-left implication
    intros arc x hx,
    have h1x : (1/x) > 0, from one_div_pos_of_pos hx,
    have h1 := arc (1/x) h1x,
    cases h1 with n hn,
    use n, split, 
    existsi n, split, refl, exact hn.left,
    set xn : ℝ := ↑n with hxn, 
    have h2n : 0 < xn, 
        rw hxn, 
        have hn0 : 0 < n, from hn.left, simp, assumption,
    exact lt_of_one_div_lt_one_div h2n hn.right,
    done
end

end xena -- hide
