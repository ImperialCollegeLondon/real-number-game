import data.real.basic

namespace xena -- hide

open function
open real

open_locale classical

/-
Classic eps-delta definition of continuity is equivalent to 
the definition using sequences.
-/

notation `|` x `|` := abs x
def is_limit (a : ℕ → ℝ) (l : ℝ) := 
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |a n - l| < ε

def continuous_at_x (f : ℝ → ℝ) (x : ℝ) := 
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, |y - x| < δ → |f y - f x| < ε
def seq_continuous_at_x (f : ℝ → ℝ) (x : ℝ) :=
    ∀ (a : ℕ → ℝ), is_limit a x → is_limit ( λ n : ℕ, f (a n) ) (f x)

/- Lemma
The two definitions of continuity are equivalent.
-/
lemma cont_iff_seq_cont (f : ℝ → ℝ) : 
    ∀ x : ℝ, continuous_at_x f x ↔ seq_continuous_at_x f x :=
begin
    intro x,
    split,
    { -- classical continuity def -> sequence def
        intros H a hax e he,
        have h1 := H e he,
        cases h1 with d hdd,
        cases hdd with hd hy,
        have h2 := hax d hd,
        cases h2 with N hN,
        use N,
        intros n hn,
        have hnd := hN n hn,
        have G := hy (a n) hnd, exact G,
    },
    { -- sequence def -> classical def is a little trickier
      -- contrapositive
      contrapose!,
      intro H, unfold continuous_at_x at H,
      push_neg at H,
      cases H with e hee,
      cases hee with he hdd,
      unfold seq_continuous_at_x, push_neg,
      -- using these hypotheses, choose a sequence 
      have k : ∀ n : ℕ, ∃ y : ℝ, |y - x| < (1:ℝ)/(n+1) ∧ e ≤ | f y - f x|, 
        intro n,
        have g1 := hdd ( (1:ℝ)/(n+1) ),
        cases g1 with g11 g12,
        exfalso,
        {  -- this seems complicated, but other ways got into coercion problems
            have f1 : ∀ m : ℕ, 0 < m+1,
                intro m, exact nat.succ_pos m,
            have f2 : ∀ m : ℕ, 0 < ( (m+1): ℝ),
                intro m, 
                have f21 := f1 m,
                norm_cast, linarith,
            have f3 : ∀ m : ℕ, 0 < 1 / ( (m+1): ℝ),
                intro m,
                have f31 := one_div_pos_of_pos (f2 m),
                exact f31,
            have f4 := f3 n,
            linarith, 
        },
        exact g12,
      choose a ha using k,
      use a,
      -- prove this sequence does converge to x
      split,
      {
        intros ε hε,
        set N := nat_ceil ( (1:ℝ)/ ε ) with hN,
        use N,
        intros n hn,
        have H := ha n, 
        cases H with h1 h2,
        have hN1 := le_nat_ceil ( (1:ℝ)/ε), rw ← hN at hN1,
        have hN2 : ((1:ℝ) / ↑N) ≤ ε, 
            exact one_div_le_of_one_div_le_of_pos hε hN1,
        have hN3 : ((1:ℝ)/(↑n+1)) < ((1:ℝ) / ↑N), 
            have hN31 : (n + 1) > N, linarith,
            have hN32 : 0 < (n+1), linarith,
            have hN33 : 0 < N, 
                have hN34 : 0 < ( (1:ℝ)/ε ), exact one_div_pos_of_pos hε,
                have hN35 := lt_of_lt_of_le hN34 hN1,
                norm_cast at hN35, exact hN35,
            apply one_div_lt_one_div_of_lt,
            norm_cast, linarith, norm_cast, linarith,
        have hN4 : ((1:ℝ)/(↑n+1)) < ε, linarith, 
        linarith,
      },
      
      { -- but f(a n) does not converge to f(x)
        unfold is_limit, push_neg,
        use e, split, exact he, 
        intro N, use N, split, linarith,
        have G := ha N, cases G with G1 G2, exact G2, 
      }, 
      done
    },
    done
end

end xena -- hide
