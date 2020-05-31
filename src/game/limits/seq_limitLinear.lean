import game.limits.L01defs
import game.limits.seq_limitTimesConst

namespace xena -- hide

notation `|` x `|` := abs x -- hide

/-
Use the previous results to obtain linearity.
-/


/- Lemma
If $\lim_{n \to \infty} a_n = \alpha$ and $\lim_{n \to \infty} b_n = \beta$
and $c$ is a constant, then 
$\lim_{n \to \infty} ( c * a_n + c * b_n) = c \alpha + c \beta$
-/
lemma lim_linear (a : ℕ → ℝ) (b : ℕ → ℝ) (α β c d : ℝ) 
    (ha : is_limit a α) (hb : is_limit b β) : 
    is_limit ( λ n, c * (a n) + d * (b n) ) (c * α + d * β) :=
begin
    apply lim_add,
    exact lim_times_const a α c ha,
    exact lim_times_const b β d hb,
    done
end

end xena -- hide

