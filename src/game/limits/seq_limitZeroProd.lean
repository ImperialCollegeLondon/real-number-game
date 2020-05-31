import game.limits.L01defs
import game.limits.seq_limitLinear

open real

namespace xena -- hide

notation `|` x `|` := abs x -- hide

/-
Use previous results to obtain the limit of a product if individual limits
for the factors are both zero.
-/


/- Lemma
If $\lim_{n \to \infty} a_n = 0$ and $\lim_{n \to \infty} b_n = 0$,
then 
$\lim_{n \to \infty} ( a_n * b_n) = 0$
-/
lemma lim_zero_prod (a : ℕ → ℝ) (b : ℕ → ℝ)
    (ha : is_limit a 0) (hb : is_limit b 0) : 
    is_limit ( λ n, (a n) * (b n) ) 0 :=
begin
    unfold is_limit,
    intros ε hε,
    set sε := sqrt ε with hsε, 
    have h1 : 0 < sε, from  real.sqrt_pos.mpr hε,
    have Ha := ha sε h1,
    have Hb := hb sε h1,
    cases Ha with Na hNa,
    cases Hb with Nb hNb,
    set N := max Na Nb with hN,
    use N,
    intros n hn,
    have Ha := hNa n (le_of_max_le_left hn),
    have Hb := hNb n (le_of_max_le_right hn),
    rw sub_zero at *, rw abs_mul, 
    have g1 := mul_lt_mul_of_pos_right Hb h1,
    have g2 : sε ^ 2 = ε, exact sqr_sqrt( le_of_lt hε),
    have g3 : sε * sε = sε ^2, ring,
    rw g3 at g1, rw g2 at g1, rw mul_comm at g1,
    have hbn : 0 ≤ |b n|, exact is_absolute_value.abv_nonneg abs (b n),
    have G := mul_le_mul_of_nonneg_right (le_of_lt Ha) hbn,
    exact lt_of_le_of_lt G g1, -- linarith fails!
    done
end

end xena -- hide


