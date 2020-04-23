import game.limits.L01defs

notation `|` x `|` := abs x -- hide
def is_limit (a : ℕ → ℝ) (l : ℝ) := 
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |a n - l| < ε

/-
Use the previous results to obtain linearity.
-/

-- begin hide
-- these should be available from previous levels
axiom lim_add_temp (a : ℕ → ℝ) (b : ℕ → ℝ) (α β : ℝ) 
    (ha : is_limit a α) (hb : is_limit b β) : 
    is_limit ( λ n, (a n) + (b n) ) (α + β)

axiom times_const_temp (a : ℕ → ℝ) (L c : ℝ) (hL : is_limit a L) : 
    is_limit (λ n, c * (a n)) (L*c) 
-- end hide

/- Lemma
If $\lim_{n \to \infty} a_n = \alpha$ and $\lim_{n \to \infty} b_n = \beta$
and $c$ is a constant, then 
$\lim_{n \to \infty} ( c * a_n + c * b_n) = c \alpha + c \beta$
-/
lemma lim_linear (a : ℕ → ℝ) (b : ℕ → ℝ) (α β c : ℝ) 
    (ha : is_limit a α) (hb : is_limit b β) : 
    is_limit ( λ n, c * (a n) + c * (b n) ) (α * c + β * c) :=
begin
    apply lim_add_temp,
    exact times_const_temp a α c ha,
    exact times_const_temp b β c hb,
    done
end

