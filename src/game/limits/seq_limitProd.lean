import game.limits.L01defs
import game.limits.seq_limSeqSub

open real

namespace xena -- hide

notation `|` x `|` := abs x -- hide

/-
Use previous results to obtain the limit of a product in the general case.
Work in progress.
-/

/- Lemma
If $\lim_{n \to \infty} a_n = \alpha$ and $\lim_{n \to \infty} b_n = \beta$, then 
$\lim_{n \to \infty} (a_n * b_n) = \alpha * \beta$
-/
lemma lim_prod (a : ℕ → ℝ) (b : ℕ → ℝ) (α β : ℝ)
    (ha : is_limit a α) (hb : is_limit b β) : 
    is_limit ( λ n, (a n) * (b n) ) (α * β) :=
begin
    have Ha := lim_seq_sub_const a α α ha,
    rw [sub_self α] at Ha,
    have Hb := lim_seq_sub_const b β β hb,
    rw [sub_self β] at Hb,
    have G := lim_zero_prod (λ n, a n - α) (λ n, b n - β) Ha Hb,
    have g1 := lim_times_const a α β ha,
    have g2 := lim_times_const b β α hb,
    -- becomes ugly, need to improve notation
    have G1 := lim_linear (λ (n : ℕ), 
        (λ (n : ℕ), a n - α) n * (λ (n : ℕ), b n - β) n) a 0 α 1 β G ha,
    have h1 : (1:ℝ) * 0 + β * α = β * α , norm_num,
    rw h1 at G1,
    have G2 := lim_linear (λ (n : ℕ), 
        1 * (λ (n : ℕ), (λ (n : ℕ), a n - α) n * (λ (n : ℕ), b n - β) n) n + β * a n) b 
        (β * α) β 1 α G1 hb,
    -- to get rid of these non-terminal `simp`
    simp at G2,
    have h2 : β * α + α * β = 2 * α * β, 
        rw mul_comm β α, norm_num, 
        have h21 := mul_two (α * β), rw ← h21, 
        rw mul_assoc α β 2, rw mul_comm β _, rw ← mul_assoc,
        rw mul_comm α 2, 
    rw h2 at G2,
    have G3 := lim_seq_sub_const 
        (λ (n : ℕ), (a n - α) * (b n - β) + (β * a n + α * b n)) (2 * α * β) (α * β) G2,
    simp at G3,
    have h3 : 2 * α * β - α * β = α * β, 
        have h31 : (2:ℝ) * α * β - α * β = (2:ℝ) * α * β + (-1:ℝ) * α * β, ring,
        --rw ← add_mul (2:ℝ) (-1:ℝ) (α * β) at h31,
        rw h31, norm_cast, norm_num, ring,
    rw h3 at G3,
    intros ε hε,
    have G4 := G3 ε hε, cases G4 with N hN,
    use N,
    intros n hn,
    have G5 := hN n hn,
    simp at G5, simp,
    have h4 : (a n - α) * (b n - β) = (a n) * (b n) - α * (b n) - β * (a n) + α * β, ring,
    rw h4 at G5,
    have h5 : a n * b n - α * b n - β * a n + α * β + (β * a n + α * b n) - α * β - α * β =
        a n * b n - α * β, ring,
    rw h5 at G5, exact G5, done
end

end xena -- hide


