import data.real.basic
import topology.algebra.infinite_sum

def partial_sum (a : ℕ → ℝ) (M : ℕ):= (finset.range M).sum a
def partial_sum_sequence (a : ℕ → ℝ ) : ℕ → ℝ := (λ (n : ℕ), partial_sum a n )

notation `|` x `|` := abs x -- hide
def is_limit (a : ℕ → ℝ) (L : ℝ) := ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
    ∀ n : ℕ, N ≤ n → |a n - L| < ε
def is_convergent (a : ℕ → ℝ) := ∃ L : ℝ, is_limit a L


