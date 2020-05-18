import data.real.basic

namespace xena -- hide

/-
# Chapter 2 : Order

## Level 3

Another property of the absolute value.
-/

notation `|` x `|` := abs x --hide

/- Lemma
For any two real numbers $a$ and $b$, we have that
$$|a| ≤ c ↔ -c ≤ a ≤ c$$.
-/
theorem abs_le (a c : ℝ) (h : 0 ≤ c): |a| ≤ c → (-c) ≤ a ∧ a ≤ c :=
begin
    rcases lt_trichotomy a 0 with haNeg | haZero | haPos,
    { -- case a < 0
        intro H, 
        have h1 : | a | = - a, exact abs_of_neg haNeg,
        rw h1 at H, split, linarith, linarith,
    },
    { -- case a = 0
        intro H, rw haZero, split, linarith, exact h,
    },
    { -- case 0 < a
        intro H,
        have h1 : |a| = a, exact abs_of_pos haPos,
        rw h1 at H, split, linarith, exact H,
    },
    done
end

end xena --hide

