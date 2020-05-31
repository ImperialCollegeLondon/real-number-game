import game.limits.L01defs
import game.limits.seq_limitZeroProd

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
    sorry,
end

end xena -- hide


