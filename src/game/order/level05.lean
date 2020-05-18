import data.real.basic

namespace xena -- hide

/-
# Chapter 2 : Order

## Level 5

Another well-known property of the absolute value.
-/

notation `|` x `|` := abs x -- hide

/- Lemma
For any two real numbers $a$ and $b$, we have that
$$| |a| - |b| | ≤ |a - b|$$.
-/
theorem abs_of_sub_le_abs (a b : ℝ) : | |a| - |b| | ≤ |a - b| :=
begin
    have h1 : a = (a - b) + b, norm_num,
    have h2 : |a| = |(a-b) + b|, rw h1, simp,
    have h3 : |(a-b) + b | ≤ |a-b| + |b|, exact abs_add _ _,
    rw ← h2 at h3,
    have h4a : |a| - |b| ≤ |a - b|, linarith,
    clear h1 h2 h3,
    have h1 : b = (b - a) + a, norm_num,
    have h2 : |b| = |(b-a) + a|, rw h1, simp,
    have h3 : |(b-a) + a | ≤ |b-a| + |a|, exact abs_add _ _,
    rw ← h2 at h3,
    have h4b : |b| - |a| ≤ |b - a|, linarith, 
    clear h1 h2 h3,
    have h1 := eq.symm ( abs_neg (a-b) ),
    have h2 : -(a-b) = b - a, norm_num,
    rw h2 at h1, clear h2,
    rw ← h1 at h4b, clear h1,
    have H : max ( |a| - |b| ) ( |b| - |a| ) ≤ | a - b |, 
        simp, split, exact h4a, exact h4b,
    unfold abs,
    unfold abs at H, 
    have G: -(max a (-a) - max b (-b)) = max b (-b) - max a (-a),
        norm_num,
    rw G,
    exact H, done,
end

end xena --hide

example (a: ℝ) : |a| = | -a| := by library_search