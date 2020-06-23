import tactic

open_locale classical -- def of max a b is "if a <= b then b else a"
noncomputable theory -- same reason

-- A linear order is a reflexive, transitive, antisymmetric and total relation `≤`

variables {X : Type} [linear_order X] {a b c : X}

-- Note in the below that sometimes we have to supply the variable names and other times not.
-- I am scared after my NNG experience to break with tradition and start
-- changing mathlib conventions. They are there for a reason (you don't need
-- them when there are implications involved, because you can guess the
-- variables from the hypotheses)

-- I think that the user would be happy to accept all of these as axioms,
-- even though strictly speaking one could define a < b to be a ≤ b ∧ a ≠ b
-- and then prove the last two. 

example : a ≤ a := le_refl a

example : a ≤ b → b ≤ c → a ≤ c := le_trans

example : a ≤ b → b ≤ a → a = b := le_antisymm

example : a ≤ b ∨ b ≤ a := le_total a b

example : a < b ↔ a ≤ b ∧ a ≠ b := lt_iff_le_and_ne

example : a ≤ b → b < c → a < c := lt_of_le_of_lt

example : a < b → b ≤ c → a < c := lt_of_lt_of_le


-- max is already defined so we work in a namespace

namespace test

-- I think this definition might be hard to work with
def max (a b : X) := if a ≤ b then b else a

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

-- but now things work really nicely. Proposal: tell them that
-- max_eq_left and max_eq_right are axioms of max, and don't
-- tell them the definition. Note that max_eq_left and max_eq_right
-- together are enough to deduce that max a b is what it is,
-- because of le_antisymm

theorem max_choice (a b : X) : max a b = a ∨ max a b = b :=
begin
  cases le_total a b with hab hba,
  { right,
    exact max_eq_right hab
  },
  { left,
    exact max_eq_left hba
  }
end

theorem max_comm (a b : X) : max a b = max b a :=
begin
  cases le_total a b with hab hba,
  { rw max_eq_right hab,
    rw max_eq_left hab,
  },
  { rw max_eq_left hba,
    rw max_eq_right hba
  }  
end

theorem le_max_left (a b : X) : a ≤ max a b :=
begin
  cases le_total a b with hab hba,
  { rw max_eq_right hab,
    assumption
  },
  { rw max_eq_left hba,
    -- Lean closes a ≤ a automatically because ≤ is reflexive
  }  
end

theorem le_max_right (a b : X) : b ≤ max a b :=
begin
  rw max_comm,
  apply le_max_left
end

-- this comes out nicely
theorem max_le (hac : a ≤ c) (hbc : b ≤ c) : max a b ≤ c :=
begin
  cases max_choice a b with ha hb,
  { rw ha,
    assumption
  },
  { rw hb,
    assumption
  }
end

-- so does this
theorem max_lt (hac : a < c) (hbc : b < c) : max a b < c :=
begin
  cases max_choice a b with ha hb,
  { rw ha,
    assumption
  },
  { rw hb,
    assumption
  }
end

-- and this, if we can teach `apply le_trans _ habc`
theorem max_le_iff : a ≤ c ∧ b ≤ c ↔ max a b ≤ c :=
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
  },
end

theorem max_lt_iff : a < c ∧ b < c ↔ max a b < c :=
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

-- long but fun
theorem le_max_iff : a ≤ max b c ↔ a ≤ b ∨ a ≤ c :=
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

-- same as previous one
theorem lt_max_iff : a < max b c ↔ a < b ∨ a < c :=
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

-- I think that's a good API for max. Let's test this hypothesis
-- by seeing how easy it is to make a good API for abs. 

end test