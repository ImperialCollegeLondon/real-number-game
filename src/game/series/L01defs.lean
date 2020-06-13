import data.real.basic
import game.series.bounded_if_convergent
--import topology.algebra.infinite_sum


namespace xena --hide 

def kth_partial_sum (a : ℕ → ℝ) (k : ℕ) := (finset.range (k+1)).sum a

def seq_partials_over (a : ℕ → ℝ ) : ℕ → ℝ := (λ (n : ℕ), kth_partial_sum a n )

notation `|` x `|` := abs x -- hide

end xena --hide
