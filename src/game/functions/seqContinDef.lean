import data.real.basic

namespace xena -- hide

open function
open real

open_locale classical

/-
Classic eps-delta definition of continuity is equivalent to 
the definition using sequences.

Work in progress!!!
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
      -- proof by contradiction
      contrapose!,
      intro H, unfold continuous_at_x at H,
      push_neg at H,
      cases H with e hee,
      cases hee with he hdd,
      unfold seq_continuous_at_x, push_neg,
      --set a := λ n, x + 1 / (2*(n+1)) with ha,
      set a : ℕ → ℝ := λ n, x + 1 / (2*(n+1)) with ha,
      use a,
      split,
      -- prove this sequence does converge to x
      intros ε hε,
      --sorry, 
      set N := ceil ( (1:ℝ) / ( (2:ℝ) * ε ) ) with hN, -- this is an integer
      have h1 :  0 ≤ N, sorry,  -- will need to prove this is positive
      have h2 := int.to_nat_of_nonneg h1, -- convert to nat
      use ↑(int.to_nat N), -- this fails if just using N ∈ ℤ 
      intros n hn,
      have h3 : a n = x + 1 / (2 * (n+1)), 
        rw ha,
      have h4 : a n - x = 1 / (2 * (n+1)), linarith,
      rw h4,
      have h5 : ( (1:ℝ) / ( (2:ℝ) * ε ) ) ≤ N, 
        rw hN, exact le_ceil _,
      have h6 : (1:ℝ) / (2 * (↑N)) ≤ ε, sorry, -- from h5
      have h7 : 1 / (2 * (↑n + 1)) < (1:ℝ) / (2 * (↑N)), sorry, -- from hn
      have h8 : 1 / (2 * (↑n + 1)) < ε, linarith,
      set t := (1:ℝ) / (2 * (↑n + 1)) with ht,
      have h9 : | t | = t, sorry,  -- prove this term is positive
      rw h9, exact h8,

      -- but f(a n) does not converge to f(x)
      sorry,


    },
    done
end

end xena -- hide
