import data.real.basic
import game.order.level01

namespace xena -- hide

/-
# Chapter 2 : Order

## Level 2

This level invites you to work out a property of the absolute value.
In Lean the absolute value of $x$ is denoted by `abs x`. 
-/

/- Hint : The definition of the absolute value in mathlib:
definition abs {α : Type u} [decidable_linear_ordered_add_comm_group α] (a : α) : α := max a (-a)
-/

/-
For ease of use, a notation can be wrapped around that definition as below.
-/

notation `|` x `|` := abs x

/- Lemma
For any two real numbers $a$ and $b$, we have that
$$|ab| = |a||b|$$.
-/
theorem abs_prod (a b : ℝ) : |a * b| = |a| * |b| :=
begin
    rcases lt_trichotomy a 0 with haNeg | haZero | haPos,
    swap,
    { -- case a = 0
        have h1 : a * b = 0, norm_num, left, exact haZero,
        have h2 : | a * b | = 0, exact (is_absolute_value.abv_eq_zero abs).mpr h1,
        have h3 : | a | = 0, exact (is_absolute_value.abv_eq_zero abs).mpr haZero,
        rw [h2,h3], norm_num,
    },
    { -- case a < 0
        rcases lt_trichotomy b 0 with hbNeg | hbZero | hbPos,
        swap,
        { -- case b = 0
            have h1 : a * b = 0, norm_num, right, exact hbZero,
            have h2 : | a * b | = 0, exact (is_absolute_value.abv_eq_zero abs).mpr h1,
            have h3 : | b | = 0, exact (is_absolute_value.abv_eq_zero abs).mpr hbZero,
            rw [h2,h3], norm_num,
        },
        { -- case b < 0
            have h1 : 0 < a * b,  exact mul_pos_of_neg_of_neg haNeg hbNeg,
            have h2 : | a * b | = a * b, exact abs_of_pos h1,
            have h3 : | a | = - a, exact abs_of_neg haNeg,
            have h4 : | b | = - b, exact abs_of_neg hbNeg,
            rw [h2, h3, h4], norm_num,
        },
        { -- case 0 < b
            have h1 : a * b < 0,  exact mul_neg_of_neg_of_pos haNeg hbPos,
            have h2 : | a * b | = - (a * b), exact abs_of_neg h1,
            have h3 : | a | = - a, exact abs_of_neg haNeg,
            have h4 : | b | = b, exact abs_of_pos hbPos,
            rw [h2, h3, h4], norm_num,
        }

    },
    { -- case 0 < a
        rcases lt_trichotomy b 0 with hbNeg | hbZero | hbPos,
        swap,
        { -- case b = 0
            have h1 : a * b = 0, norm_num, right, exact hbZero,
            have h2 : | a * b | = 0, exact (is_absolute_value.abv_eq_zero abs).mpr h1,
            have h3 : | b | = 0, exact (is_absolute_value.abv_eq_zero abs).mpr hbZero,
            rw [h2,h3], norm_num,
        },
        { -- case b < 0
            have h1 : a * b < 0,  exact mul_neg_of_pos_of_neg haPos hbNeg,
            have h2 : | a * b | = -( a * b), exact abs_of_neg h1,
            have h3 : | a | = a, exact abs_of_pos haPos,
            have h4 : | b | = - b, exact abs_of_neg hbNeg,
            rw [h2, h3, h4], norm_num,
        },
        { -- case 0 < b
            have h1 : 0 < a * b,  exact mul_pos haPos hbPos,
            have h2 : | a * b | = a * b, exact abs_of_pos h1,
            have h3 : | a | = a, exact abs_of_pos haPos,
            have h4 : | b | = b, exact abs_of_pos hbPos,
            rw [h2, h3, h4],  -- this is enough, rw closes the refl goal 
        }

    },
    done

end

end xena --hide
