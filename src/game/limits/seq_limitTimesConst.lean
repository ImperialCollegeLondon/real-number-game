import data.real.basic

notation `|` x `|` := abs x -- hide
def is_limit (a : ℕ → ℝ) (l : ℝ) := 
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |a n - l| < ε

lemma limit.times_const (a : ℕ → ℝ) (L c : ℝ) (hL : is_limit a L) : 
    is_limit (λ n, c * (a n)) (L*c) :=
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
    set b := a n - L with hb,
    have E := F b,
    rw hb at E,
    have D := mul_sub c (a n) L,
    rw D at E, 
    rw mul_comm c L at E, rw ← hb at E,
    linarith,
  },
  {
    intros ε hε,
    cases hL ε hε with M hM,
    use M, intros n hn, simp,
    have H : c * (a n) = 0, norm_num, left, exact hc, rw H,
    have G : L * c = 0, norm_num, right, exact hc, rw G,
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
    set b := a n - L with hb,
    have E := F b,
    have D : |c| = c, exact abs_of_pos hc,
    rw D at E, rw hb at E,
    have C := mul_sub c (a n) L,
    rw C at E, 
    rw mul_comm c L at E, rw ← hb at E,
    linarith,
  }, 
  done
end

