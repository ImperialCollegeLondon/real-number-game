import data.real.basic
open function
open real

/-
Classic eps-delta definition of continuity is equivalent to 
the definition using sequences.

Work in progress.
-/

notation `|` x `|` := abs x
def is_limit (a : ℕ → ℝ) (l : ℝ) := 
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |a n - l| < ε

def continuous_at_x (f : ℝ → ℝ) (x : ℝ) := 
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, |x - y| < δ → |f x - f y| < ε
def continuous_at_x_seq (f : ℝ → ℝ) (x : ℝ) :=
    ∀ (a : ℕ → ℝ), is_limit a x → is_limit ( λ n : ℕ, f (a n) ) (f x)

/- Lemma
The two definitions of continuity are equivalent.
-/
lemma continuous_iff (f : ℝ → ℝ) : 
    ∀ x : ℝ, continuous_at_x f x ↔ continuous_at_x_seq f x :=
begin
    sorry,
end
