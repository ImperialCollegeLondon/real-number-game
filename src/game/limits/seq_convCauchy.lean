import game.limits.L01defs
import game.limits.seq_proveLimit

namespace xena -- hide

notation `|` x `|` := abs x -- hide

def is_convergent (a : ℕ → ℝ) := ∃ L : ℝ, is_limit a L
def is_Cauchy (a : ℕ → ℝ) := 
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ, N ≤ n ∧ m ≤ N → |a m - a n| < ε

/-
Relationship convergent/Cauchy sequences.

Work in progress.
-/

/- Lemma
A sequence of real numbers is convergent if and only if it is
a Cauchy sequence.
-/
lemma conv_iff_cauchy (a : ℕ → ℝ) : 
    is_convergent a ↔ is_Cauchy a :=
begin
  sorry,
end

end xena -- hide

