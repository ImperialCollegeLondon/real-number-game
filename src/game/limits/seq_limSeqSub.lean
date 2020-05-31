import game.limits.L01defs
import game.limits.seq_limitZeroProd

open real

namespace xena -- hide

notation `|` x `|` := abs x -- hide

/-
Use previous results to obtain the limit of a product in the general case.
-/

/- Lemma
If $\lim_{n \to \infty} a_n = \alpha$, then 
$\lim_{n \to \infty} (a_n - \alpha) = 0.$
-/
lemma lim_seq_sub_limit (a : ℕ → ℝ) (α : ℝ)
    (ha : is_limit a α) : 
    is_limit ( λ n, (a n) - α ) 0 :=
begin
    intros ε hε,
    have H := ha ε hε, cases H with N hN,
    use N, intros n hn, 
    have G := hN n hn, rw sub_zero, simpa, done
end

end xena
