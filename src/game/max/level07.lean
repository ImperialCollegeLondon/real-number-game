import game.max_and_abs.level06 -- hide

open_locale classical -- hide

noncomputable theory -- hide

namespace xena -- hide

/-
# Chapter ? : Max and abs

## Level 7

`max_lt` and `max_lt_iff` are equally useful. Let's knock them off
using the same techniques.
-/

/- Lemma
If $a$, $b$, $c$ are real numbers with $a<c$ and $b<c$,
then $\max(a,b)<c.$
-/
theorem max_lt {a b c : ℝ} (hac : a < c) (hbc : b < c) : max a b < c :=
begin
  cases max_choice a b with ha hb,
  { rw ha,
    assumption
  },
  { rw hb,
    assumption
  }


  
end

end xena --hide
