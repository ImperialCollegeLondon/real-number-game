import tactic -- hide

import data.real.basic -- imports the real numbers

open_locale classical -- allow proofs by contradiction
noncomputable theory -- don't fuss about the reals being uncomputable

namespace xena -- hide

-- Let a, b, c be real numbers
variables {a b c : ℝ}

/-
# Chapter ? : Max and abs

## Level 1

In this chapter we develop a basic interface for the `max a b` and `abs a`
function on the real numbers. Before we start, you will need to know
the basic API for `≤` and `<`, which looks like this:

```
example : a ≤ a := le_refl a

example : a ≤ b → b ≤ c → a ≤ c := le_trans

example : a ≤ b → b ≤ a → a = b := le_antisymm

example : a ≤ b ∨ b ≤ a := le_total a b

example : a < b ↔ a ≤ b ∧ a ≠ b := lt_iff_le_and_ne

example : a ≤ b → b < c → a < c := lt_of_le_of_lt

example : a < b → b ≤ c → a < c := lt_of_lt_of_le
```

/- Axiom : le_refl :
le_refl (a : ℝ) : a ≤ a
-/

/- Axiom : le_trans :
le_trans : a ≤ b → b ≤ c → a ≤ c
-/

/- Axiom : le_antisymm :
le_antisymm : a ≤ b → b ≤ a → a = b
-/

/- Axiom : le_total :
le_total a b : a ≤ b ∨ b ≤ a
-/

/- Axiom : lt_iff_le_and_ne :
lt_iff_le_and_ne : a < b ↔ a ≤ b ∧ a ≠ b
-/

/- Axiom : lt_of_le_of_lt :
lt_of_le_of_lt : a ≤ b → b < c → a < c 
-/

/- Axiom : lt_of_lt_of_le :
lt_of_lt_of_le : a < b → b ≤ c → a < c
-/

We start with `max a b := if a ≤ b then b else a`. It is
uniquely characterised by the following two properties, which are hence
all you will need to know:

```
theorem max_eq_right : a ≤ b → max a b = b

theorem max_eq_left : b ≤ a → max a b = a
```

/- Axiom : max_eq_right :
max_eq_right : a ≤ b → max a b = b
-/

/- Axiom: max_eq_left :
theorem max_eq_left : b ≤ a → max a b = a
-/

-/
-- begin hide
def max (a b : ℝ) := if a ≤ b then b else a

-- need if_pos to do this one
theorem max_eq_right (hab : a ≤ b) : max a b = b :=
begin
  unfold max,
  rw if_pos hab,  
end

-- need if_neg to do this one
theorem max_eq_left (hba : b ≤ a) : max a b = a :=
begin
  by_cases hab : a ≤ b,
  { rw max_eq_right hab,
    exact le_antisymm hba hab,
  },
  { unfold max,
    rw if_neg hab,
  }
end
-- end hide

/- Hint : Hint
Do a case split with `cases le_total a b`. 
-/

/- Lemma
For any two real numbers $a$ and $b$, either $\max(a,b) = a$
or $\max(a,b) = b$.
-/
theorem max_choice (a b : ℝ) : max a b = a ∨ max a b = b :=
begin
  cases le_total a b with hab hba,
  { right,
    exact max_eq_right hab
  },
  { left,
    exact max_eq_left hba
  }



end

end xena --hide
