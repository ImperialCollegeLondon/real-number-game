import game.limits.L01defs
import game.limits.seq_lim_add

namespace xena -- hide

notation `|` x `|` := abs x -- hide

/-
A basic result for working with sequences.
-/

/- Lemma
If $\lim_{n \to \infty} a_n = \alpha$ and $c \in \mathbb{R}$, then
 $\lim_{n \to \infty} (c \cdot a_n) = c \cdot \alpha$
-/
lemma lim_times_const (a : ℕ → ℝ) (α c : ℝ) (hL : is_limit a α) : 
    is_limit (λ n, c * (a n)) (c*α) :=
begin
  rcases lt_trichotomy c 0 with hc | hc | hc,
  {
    intros ε hε,
    set e := ε / |c| with he,
    have cnz : c ≠ 0, linarith,
    have habsc := abs_pos_iff.mpr cnz,
    have he_pos := div_pos hε habsc,
    cases hL e he_pos with M hM,
    use M, intros n hn, rw he at hM, simp,
    have H := hM n hn,
    have G := (lt_div_iff' habsc).mp H,
    have F := abs_mul c,
    set b := a n - α with hb,
    have E := F b,
    rw hb at E,
    have D := mul_sub c (a n) α,
    rw D at E, 
    rw ← hb at E,
    linarith,
  },
  {
    intros ε hε,
    cases hL ε hε with M hM,
    use M, intros n hn, simp,
    have H : c * (a n) = 0, norm_num, left, exact hc, rw H,
    have G : c * α = 0, norm_num, left, exact hc, rw G,
    norm_num, exact hε,
  },
  { -- this can be merged with first case
    intros ε hε,
    set e := ε / c with he,
    have he_pos := div_pos hε hc,
    cases hL e he_pos with M hM,
    use M, intros n hn, rw he at hM, simp,
    have H := hM n hn,
    have G := (lt_div_iff' hc).mp H,
    have F := abs_mul c,
    set b := a n - α with hb,
    have E := F b,
    have D : |c| = c, exact abs_of_pos hc,
    rw D at E, rw hb at E,
    have C := mul_sub c (a n) α,
    rw C at E, 
    rw ← hb at E,
    linarith,
  }, 
  done
end

end xena -- hide

