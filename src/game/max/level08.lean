import game.max_and_abs.level05 -- hide

open_locale classical -- hide

noncomputable theory -- hide

namespace xena -- hide

/-
# Chapter ? : Max and abs

## Level 8

See if you can do `max_lt_iff` without introducing
any auxiliary hypotheses with `have`. Don't forget to
check the list of theorems to see the interface for `≤`
and `<`.
-/

/- Lemma
If $a$, $b$, $c$ are real numbers,
then ($a<c$ and $b<c$) iff $\max(a,b)<c.$
-/

theorem max_lt_iff {a b c : ℝ} : a < c ∧ b < c ↔ max a b < c :=
begin
  split,
  { intro h,
    cases h with hac hbc,
    exact max_lt hac hbc
  },
  { intro habc,
    split,
    { apply lt_of_le_of_lt _ habc,
      apply le_max_left},
    { apply lt_of_le_of_lt _ habc,
      apply le_max_right
    }
  },
end

end xena --hide
