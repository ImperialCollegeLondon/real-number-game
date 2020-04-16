import game.limits.L01defs

notation `|` x `|` := abs x -- hide
def is_limit (a : ℕ → ℝ) (l : ℝ) := ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 
    ∀ n : ℕ, N ≤ n → |a n - l| < ε

/-
Another basic result for working with sequences.
-/

/- Lemma
If $\lim_{n \to \infty} a_n = \alpha$ and $\lim_{n \to \infty} b_n = \beta$, then
 $\lim_{n \to \infty} (a_n + b_n) = \alpha + \beta$
-/
lemma lim_add (a : ℕ → ℝ) (b : ℕ → ℝ) (α β : ℝ) 
    (ha : is_limit a α) (hb : is_limit b β) : 
    is_limit ( λ n, (a n) + (b n) ) (α + β) :=
begin
   sorry,
end

