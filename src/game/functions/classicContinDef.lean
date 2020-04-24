import data.real.basic
open function
open real

/-
Classic eps-delta definition of continuity.
Use it to prove continuity at one point for a simple function.
To be proved equivalent to topological definition in topology world.

Work in progress.
-/

notation `|` x `|` := abs x

def continuous_at_x (f : ℝ → ℝ) (x : ℝ) := 
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ → ∀ y : ℝ, |x - y| < δ → |f x - f y| < ε
def square_f (x : ℝ) := x^2

/- Lemma
The function $f(x) = x^2$ is continuous at $x=3$.
-/
lemma square_continuous_at_3 : continuous_at_x square_f (3:ℝ) :=
begin
    intros ε hε,
    set d := min (1:ℝ) (ε/7) with hdefd,
    use d,
    -- is this ok? Should need to prove d > 0 -- ?
    intro hd,
    intros y hy,
    unfold square_f,
    have H : 3^2 - y^2 = (3-y)*(3+y), ring,
    have G : | 3^2 - y^2 | = | (3-y)*(3+y) |, rw H,
    have F : | (3-y)*(3+y) | = |3-y| * |3+y|, exact abs_mul _ _,
    rw F at G, rw G,
    have h1 := abs_lt.1 hy,
    cases h1 with h11 h12,
    have h1y : y < 3 + d, linarith,
    have h2y : 3 - d < y, linarith,
    have hdd : d ≤ 1, exact min_le_left (1:ℝ) (ε/7),
    have h3y : y < 4, linarith,
    have h4y : 2 < y, linarith,
    have h44 : 0 < |3+y|, 
        have h45 : 0 < 3 + y, linarith, 
        have h46 := abs_of_pos h45,
        rw ← h46 at h45, exact h45,
    have h5y :=  (mul_lt_mul_right h44).mpr hy,
    have h6y : 3+y < 7, linarith, 
    have h7y : |3+y| < 7, 
        have h45 : 0 < 3 + y, linarith, --reusing, should only do once
        have h46 := abs_of_pos h45,
        rw ← h46 at h6y, exact h6y,
    have D := (mul_lt_mul_right hd).mpr h7y,
    rw mul_comm at D, rw mul_comm 7 d at D,
    have h9y : |3 - y| * |3 + y| <  d * 7, linarith,
    have h10y : d ≤ (ε/7), exact min_le_right (1:ℝ) (ε/7),
    have h11y : |3 - y| * |3 + y| < (ε/7) * 7, linarith,
    have h12y : (ε/7) * 7 = ε, linarith,
    rw h12y at h11y, exact h11y,
end