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
  --classical proof for boundedness of Cauchy sequences
  intro HC,
  set e := (1:ℝ),
  have h1e : (0:ℝ) < 1, linarith,
  have H := HC 1 h1e,
  cases H with N hN,
  have G := hN N,
  -- construct X = {|a0|, |a1|, ...,|am|}
  let X := finset.image (abs ∘ a) (finset.range (N + 1)),
  -- at least a0 is in X
  have  ha0 : |a 0| ∈ X := finset.mem_image_of_mem _ (mem_range.2 (nat.zero_lt_succ _)),
  -- hence the set X is not empty
  have ha1 : X ≠ ∅ := ne_empty_of_mem ha0,
  have ha2 := nonempty_iff_ne_empty.mpr ha1,
  -- and therefore has a maximum
  let B1 := X.max' ha2,
  -- If n ≤ m then get a proof that |a n| ≤ B1.
  have HB1 : ∀ n ≤ N, |a n| ≤ B1 := λ n Hn, le_max' X ha2 _
    (mem_image_of_mem _ (mem_range.2 (nat.lt_succ_of_le Hn))),
  -- term that bounds all members of the sequence
  set B := max B1 ( |a N| + 1 ) with hB,
  -- so this will be our bound
  use B,
  split,
  swap,
  intro n,
  cases le_or_gt n N with hn1 hn2,
  { -- n ≤ N
    have g1 : | a n | ≤  B1 := HB1 n hn1,
    have g2 : B1 ≤ B := le_max_left _ _, 
    linarith,
  },
  { -- n > N
    have g1 := G n,
    have g2 : N ≤ N ∧ N ≤ n,
        split; linarith,
    have g3 := g1 g2,
    rw abs_lt at g3,
    have fact1 := g3.left,
    have fact2 := g3.right,
    simp,
    right,
    rw abs_le,  -- our abs_le is conditional on 0 ≤ c - proven in the last section
    simp,
    split,
    {
    have simplefact1: - a N ≤ | a N | := neg_le_abs_self (a N),
    linarith,
    },   
    {have simplefact2: a N ≤ | a N | := le_abs_self(a N),
    linarith},
    
  have simplefact3: 0 ≤ |a N|, from abs_nonneg (a N),
  linarith,     
  },
  
  have g1 : |a N| + 1 ≤ B := le_max_right _ _,
  have g2: 0 ≤ |a N|, from abs_nonneg (a N),
  linarith,

end

end xena -- hide

