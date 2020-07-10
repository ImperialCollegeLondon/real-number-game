import game.max.level05 -- hide

open_locale classical -- hide

noncomputable theory -- hide

namespace xena -- hide

/-
# Chapter ? : Max and abs

## Level 6

In fact `max_le` can be beefed up to an iff statement.
-/

/- Hint : Tip : using `le_trans` 
If your goal is `x ≤ z` and you have a hypothesis `h : y ≤ z`
then of course it will suffice to prove `x ≤ y` and then you
can use transitivity. Instead of `have hxy : x ≤ y,`, opening
a new goal and adding a new hypothesis to our list, you can
do 

```
apply le_trans _ h
```

or

```
refine le_trans _ h
```

and this just reduces the goal to proving `x ≤ y` immediately. 

-/

/- Lemma
If $a$, $b$, $c$ are real numbers,
then ($a\leq c$ and $b\leq c$) iff $\max(a,b)\leq c.$
-/

theorem max_le_iff {a b c : ℝ} : a ≤ c ∧ b ≤ c ↔ max a b ≤ c :=
begin
  split,
  { intro h,
    cases h with hac hbc,
    exact max_le hac hbc
  },
  { intro habc,
    split,
    { apply le_trans _ habc,
      apply le_max_left},
    { apply le_trans _ habc,
      apply le_max_right
    }
  }
end

end xena --hide

/- Hint : Solution
  split,
  { intro h,
    cases h with hac hbc,
    exact max_le hac hbc
  },
  { intro habc,
    split,
    { apply le_trans _ habc,
      apply le_max_left},
    { apply le_trans _ habc,
      apply le_max_right
    }
  }
-/
