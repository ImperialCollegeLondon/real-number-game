import game.limits.L01defs
import game.limits.seq_limitLinear

notation `|` x `|` := abs x -- hide

namespace xena -- hide

/-
A simple limit proof.
-/

-- begin hide
-- The proof below is from M1P1-lean.
-- end hide

/- Lemma
Prove that the limit of $a_n = 1/n$ is zero.
-/
theorem limit_check : is_limit (λ n, 1 / n) 0 :=
begin
  -- say ε is a positive real
  intros ε Hε,
  -- we need to find N such that n ≥ N → |1 / n| < ε.
  -- It's a standard fact there exists some integer M ≥ 0
  -- such that 1 / (M + 1) < ε...
  cases (exists_nat_one_div_lt Hε) with M HM,
  -- ...so let's set N = M + 1.
  let N := M + 1,
  use N,
  -- Now say n ≥ N.
  intros n Hn, change N ≤ n at Hn,
  -- We need to show |1/n| < ε (because 1/n = 1/n - 0)
  rw sub_zero, show abs ((1 : ℝ) / n) < ε,
  -- Because n ≥ N = M + 1 ≥ 1 > 0, we have n > 0
  have HM' : 0 < N := lt_of_lt_of_le zero_lt_one (by simp),
  have HM'' : (0 : ℝ) < N := 
    by rwa [←nat.cast_zero,nat.cast_lt],
    -- note to self -- Lean rewriting M + 1 as 1 + M
  have HNn : (N : ℝ) ≤ n := by rwa nat.cast_le,
  have Hn'' : 0 < (n : ℝ) := by linarith,
  -- so 1 / n > 0,
  have H2 : (1 : ℝ) / n > 0,
    exact one_div_pos_of_pos Hn'',
  -- and hence |1 / n| = 1 / n.
  rw abs_of_pos H2,
  -- We want to prove 1 / n < ε, but we know 1 / N < ε,
  -- so it suffices to prove 1 / n ≤ 1 / N
  suffices : (1 : ℝ) / n ≤ 1 / N,
    exact lt_of_le_of_lt this HM,
  -- This follows easily from the fact that N ≤ n
  refine div_le_div_of_le_left zero_le_one HM'' HNn,
  done
end

end xena -- hide
