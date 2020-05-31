import game.limits.L01defs
import game.limits.seq_limSeqSub

open real

namespace xena -- hide

notation `|` x `|` := abs x -- hide

/-
Use previous results to obtain the limit of a product in the general case.
-/

/- Lemma
If $\lim_{n \to \infty} a_n = \alpha$ and $\lim_{n \to \infty} b_n = \beta$, then 
$\lim_{n \to \infty} (a_n * b_n) = \alpha * \beta$
-/
lemma lim_prod (a : ℕ → ℝ) (b : ℕ → ℝ) (α β : ℝ)
    (ha : is_limit a α) (hb : is_limit b β) : 
    is_limit ( λ n, (a n) * (b n) ) (α * β) :=
begin
    --intros ε hε,
    have Ha := lim_seq_sub_limit a α ha,
    have Hb := lim_seq_sub_limit b β hb, 
    have G := lim_zero_prod (λ n, a n - α) (λ n, b n - β) Ha Hb,
    have g1 := lim_times_const a α β ha,
    have g2 := lim_times_const b β α hb,
    have G1 := lim_linear (λ (n : ℕ), 
        (λ (n : ℕ), a n - α) n * (λ (n : ℕ), b n - β) n) a 0 α 1 β G ha,
    -- becomes ugly, need to improve notation
    sorry,
end

end xena -- hide


