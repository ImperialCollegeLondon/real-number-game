import game.limits.L01defs
import game.limits.seq_proveLimit
import algebra.pi_instances
import game.order.level05


--open function
open finset

namespace xena -- hide

notation `|` x `|` := abs x -- hide

def is_convergent (a : ℕ → ℝ) := ∃ α : ℝ, is_limit a α 
def is_Cauchy (a : ℕ → ℝ) := 
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m ∧ N ≤ n → |a m - a n| < ε
def is_bdd (a : ℕ → ℝ) := ∃ B > 0, ∀ n, |a n| ≤ B 

-- begin hide
-- We may want to skip this in RNG unless we can make it look (or be) easy --?
-- end hide

/-
Cauchy sequences are bounded.

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
  have h1e : (0:ℝ) < e, linarith,
  have H := HC e h1e,
  cases H with m hm,
  have G := hm m,
  -- construct X = {|a0|, |a1|, ...,|am|}
  let X := finset.image (abs ∘ a) (finset.range (m + 1)),
  -- a0 is in X
  have  ha0 : |a 0| ∈ X := finset.mem_image_of_mem _ (mem_range.2 (nat.zero_lt_succ _)),
  -- thus X is not empty
  have ha1 : X ≠ ∅ := ne_empty_of_mem ha0,
  have ha2 := nonempty_iff_ne_empty.mpr ha1,
  -- and therefore has a maximum
  let B1 := max' X ha2,
  -- If n ≤ m then get a proof that |a n| ≤ B1.
  have HB1 : ∀ n ≤ m, |a n| ≤ B1 := λ n Hn, le_max' X ha2 _
    (mem_image_of_mem _ (mem_range.2 (nat.lt_succ_of_le Hn))),
  -- term that bounds all members of the sequence
  set B := max B1 ( |a m| + 1 ) with hB,
  -- so this will be our bound
  use B,
  split,
  swap,
  intro n,
  cases le_or_gt n m with hn1 hn2,
  { -- n ≤ m
    have g1 : | a n | ≤  B1 := HB1 n hn1,
    have g2 : B1 ≤ B := le_max_left _ _, 
    linarith,
  },
  { -- n > m
    have g1 := G n,
    have g2 : m ≤ m ∧ m ≤ n,
        split; linarith,
    have g3 := g1 g2, 
    have g4 : | a n | ≤ |a m| + 1,
        have g41 := abs_of_sub_le_abs (a m) (a n),
        have g42 : | |a m| - |a n| | < e, linarith,
        have g43 := abs_le ( |a m| - |a n| ) e (le_of_lt h1e) (le_of_lt g42),
        cases g43 with g44 g45, linarith,
    have g5 : |a m| + 1 ≤ B := le_max_right _ _,
    linarith,
  },
  -- almost done; need B > 0; linarith needs a little help
  have g1 : |a m| + 1 ≤ B := le_max_right _ _,
  have g2 : 0 ≤ |a m|,  exact is_absolute_value.abv_nonneg abs (a m),
  have g3 : 1 ≤ |a m| + 1, linarith,
  --have g4 : 0 < 1, linarith, 
  linarith,

end

end xena -- hide

