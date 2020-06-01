import game.limits.L01defs
import game.limits.seq_proveLimit

namespace xena -- hide

notation `|` x `|` := abs x -- hide

def is_convergent (a : ℕ → ℝ) := ∃ α : ℝ, is_limit a α 
def is_Cauchy (a : ℕ → ℝ) := 
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m ∧ N ≤ n → |a m - a n| < ε
def is_bdd (a : ℕ → ℝ) := ∃ B > 0, ∀ n, |a n| < B 

/-
Cauchy sequences are bounded.

Work in progress.
-/

/- Lemma
A Cauchy sequence is bounded.
-/
lemma cauchy_is_bdd (a : ℕ → ℝ) : 
    is_Cauchy a → is_bdd a:=
begin
  -- classical proof for boundedness of Cauchy sequences
  intro HC,
  set e := (1:ℝ) with he,
  have h1 : (0:ℝ) < e, linarith,
  have H := HC e h1,
  cases H with m hm,
  have G := hm m,
  -- this doesn't seem to exist the way I was hoping
  --let B := ((finset.range m).max a)
  -- can get a proof of the existence of a maximum though
  sorry,


end

end xena -- hide

--begin hide
variable m : ℕ 
variable a : ℕ → ℝ 
#check (finset.range m).sum a 
#check (finset.range m).max
-- need a proof that finset.range m is not empty.
#check finset.exists_max_image (finset.range m) a
#check max
-- end hide
