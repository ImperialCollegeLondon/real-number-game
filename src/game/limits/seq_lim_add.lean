import game.limits.L01defs
import game.sup_inf.GLBprop_if_LUBprop


namespace xena -- hide

notation `|` x `|` := abs x -- hide

/-
Another basic result for working with sequences.
-/

/- Lemma
If $\lim_{n \to \infty} a_n = \alpha$ and $\lim_{n \to \infty} b_n = \beta$, then
 $\lim_{n \to \infty} (a_n + b_n) = \alpha + \beta$
-/
lemma lim_add (a : ℕ → ℝ) (b : ℕ → ℝ) (α β : ℝ) 
    (ha : is_limit a α) (hb : is_limit b β) : 
    is_limit ( λ n, (a n) + (b n) ) (α + β) :=
begin
   intros ε hε,
   set e := ε / 2 with hedef,
   have he : 0 < e, linarith,
   have Ha := ha e he,
   have Hb := hb e he,
   cases Ha with na hna,
   cases Hb with nb hnb,
   set m := max na nb with hm,
   have hm1 : m ≥ na, norm_num, left, linarith,
   have hm2 : m ≥ nb, norm_num, right, linarith,
   use m,
   intros n hn,
   have hn1 : n ≥ na, linarith,
   have hn2 : n ≥ nb, linarith,
   have H1 := hna n hn1,
   have H2 := hnb n hn2,
   have H := abs_add (a n - α) (b n - β),
   simp, 
   have G : a n - α + (b n - β) = a n + b n - (α + β), linarith,
   rw G at H,
   have F : |a n - α| + |b n - β| < 2 * e, linarith,
   have E : |a n + b n - (α + β)| < 2 * e, linarith,
   have D : 2 * e = ε, linarith,
   rw D at E, exact E, done
end

end xena -- hide

