import game.max.level09 -- hide

open_locale classical -- hide

noncomputable theory -- hide

namespace xena -- hide

/-
# Chapter 1 : Max

## Level 10

And finally `lt_max_iff`. 
-/

/- Lemma
If $a$, $b$, $c$ are real numbers,
then $a<\max(b,c)$ iff ($a<b$ or $a<c$).
-/

theorem lt_max_iff {a b c : ℝ} : a < max b c ↔ a < b ∨ a < c :=
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
    { apply lt_of_lt_of_le hab,
      apply le_max_left},
    { apply lt_of_lt_of_le hac,
      apply le_max_right},
  }
end

end xena --hide
