import data.real.basic

namespace xena -- hide

open function
open real

open_locale classical

/-
Classic eps-delta definition of continuity is equivalent to 
the definition using sequences.

Work in progress.
-/

notation `|` x `|` := abs x
def is_limit (a : ℕ → ℝ) (l : ℝ) := 
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |a n - l| < ε

def continuous_at_x (f : ℝ → ℝ) (x : ℝ) := 
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, |y - x| < δ → |f y - f x| < ε
def continuous_at_x_seq (f : ℝ → ℝ) (x : ℝ) :=
    ∀ (a : ℕ → ℝ), is_limit a x → is_limit ( λ n : ℕ, f (a n) ) (f x)

/- Lemma
The two definitions of continuity are equivalent.
-/
lemma cont_iff_seq_cont (f : ℝ → ℝ) : 
    ∀ x : ℝ, continuous_at_x f x ↔ continuous_at_x_seq f x :=
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
      unfold continuous_at_x_seq, push_neg,
      let a : ℕ → ℝ := λ n, x + 1 / (2*(n+1)),
      use a,
      split,
      -- prove this sequence does converge to x
      intros ε hε,
      sorry, -- use ceil ( (1:ℝ)/((2:ℝ)*ε)  ), -- this fails

      -- but f(a n) does not converge to f(x)
      sorry,


    },
    done
end

end xena -- hide

