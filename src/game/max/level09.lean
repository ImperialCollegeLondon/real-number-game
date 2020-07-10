import game.max.level08 -- hide

open_locale classical -- hide

noncomputable theory -- hide

namespace xena -- hide

/-
# Chapter 1 : Max

## Level 9

We've done `max_le_iff`; here is `le_max_iff`. 
-/

/- Lemma
If $a$, $b$, $c$ are real numbers,
then $a\leq\max(b,c)$ iff ($a\leq b$ or $a\leq c$).
-/

theorem le_max_iff {a b c : ℝ} : a ≤ max b c ↔ a ≤ b ∨ a ≤ c :=
begin
  split,
  { intro ha,
    cases le_total b c with hbc hcb,
    { rw max_eq_right hbc at ha,
      right,
      assumption,
    },
    { rw max_eq_left hcb at ha,
      left,
      assumption
    }
  },
  { intro habc,
    cases habc with hab hac,
    { apply le_trans hab,
      apply le_max_left},
    { apply le_trans hac,
      apply le_max_right},
  }
end

end xena --hide
