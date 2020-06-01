import game.limits.L01defs
import game.limits.seq_proveLimit

namespace xena -- hide

notation `|` x `|` := abs x -- hide

def is_convergent (a : ℕ → ℝ) := ∃ α : ℝ, is_limit a α 
def is_Cauchy (a : ℕ → ℝ) := 
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m ∧ N ≤ n → |a m - a n| < ε

/-
Relationship convergent/Cauchy sequences.

Work in progress.
-/

/- Lemma
A convergent sequence of real numbers is a Cauchy sequence.
-/
lemma conv_iff_cauchy (a : ℕ → ℝ) : 
    is_convergent a →  is_Cauchy a :=
begin
  --split,
  -- left-right implication: just doing convergent -> Cauchy here
  -- for the other direction should prove boundedness of Cauchy first
  intros h e he,
  set e2 := e / 2 with hde2,
  have he2 : 0 < e2, from half_pos he,
  cases h with α hα, 
  have H := hα e2 he2,
  cases H with N hN,
  use N,
  intros m n hmn,
  have hm := hN m hmn.1, 
  have hn := hN n hmn.2,
  have h1 : a m - a n = (a m - α) + (α - a n), ring,
  have h2 : | (a m - α) + (α - a n) | ≤ | a m - α | + | α - a n |,
    exact abs_add (a m - α) (α - a n),
  rw h1,
  have g1 : |a n - α| = |α - a n|, 
    have g11 : a n - α = - ( α - a n), norm_num,
    rw g11, exact abs_neg _,
  rw g1 at hn,
  linarith,
  -- right-left implication
  --intro H,
  --sorry,


end

end xena -- hide

-- begin hide
--example (a b c d : ℝ) (h1 : a ≤ b + c) : a - b ≤ c  := by library_search
--example ( a : ℝ ) : |a| = | - a | := by library_search
-- end hide

