import game.max_and_abs.max_API_test
import data.real.basic

noncomputable theory

namespace test

variables {a b c : ℝ}

-- What ℝ has that a general total order hasn't got, is - .

example : -a ≤ -b ↔ b ≤ a := by split; intros; linarith

def abs (x : ℝ) := max x (-x)

-- useful for rewriting
lemma abs_def (x : ℝ) : abs x = max x (-x) := rfl

-- needs congr'
lemma abs_neg (x : ℝ) : abs (-x) = abs x :=
begin
  rw abs_def,
  rw abs_def,
  rw max_comm,
  congr',
  ring,
end

-- order level 3
-- Powerful. Teaches them the colon. 
theorem abs_le : abs a ≤ b ↔ -b ≤ a ∧ a ≤ b :=
begin
  rw abs_def,
  rw ←max_le_iff,
  split;
  intro h;
  cases h;
  split;
  linarith,
end

theorem abs_of_nonneg (h : 0 ≤ a) : abs a = a :=
begin
  rw abs_def,
  apply max_eq_left,
  linarith
end

theorem abs_of_nonpos (h : a ≤ 0) : abs a = -a :=
begin
  rw abs_def,
  apply max_eq_right,
  linarith
end

variables (a b) -- want them explicit in the next few

theorem abs_add : abs (a + b) ≤ abs a + abs b :=
begin
  rw abs_le,
  cases le_total 0 a with h0a ha0,
  { -- 0 ≤ a
    rw abs_of_nonneg h0a,
    cases le_total 0 b with h0b hb0,
    { rw abs_of_nonneg h0b,
      split; linarith
    },
    { rw abs_of_nonpos hb0,
      split; linarith
    },
  },
  { -- a ≤ 0
    rw abs_of_nonpos ha0,
    cases le_total 0 b with h0b hb0,
    { rw abs_of_nonneg h0b,
      split; linarith
    },
    { rw abs_of_nonpos hb0,
      split; linarith
    },
  },
end

-- order level 4
-- convert makes this simple
theorem abs_sub_le_add_abs : abs (a - b) ≤ abs a + abs b :=
begin
  rw ←abs_neg b,
  convert abs_add a (-b),
end

-- order level 5
-- combination of ring and linarith; always try and deduce from triangle ineq
theorem abs_abs_sub_le_abs_sub : abs (abs a - abs b) ≤ abs (a - b) :=
begin
  rw abs_le,
  split,
  { have h := abs_sub_le_add_abs a (a - b),
    ring at h,
    linarith,
  },
  { have h := abs_sub_le_add_abs (a - b) (-b),
    rw abs_neg at h,
    ring at h,
    linarith
  }
end

-- order level 2
theorem abs_mul (a b : ℝ) : abs (a * b) = abs a * abs b :=
begin
  cases le_total 0 a with h0a ha0;
  cases le_total 0 b with h0b hb0,
  { -- both nonnegative
    rw abs_of_nonneg h0a,
    rw abs_of_nonneg h0b,
    rw abs_of_nonneg,
    nlinarith,
  },
  { -- b <= 0 <= a
    rw abs_of_nonneg h0a,
    rw abs_of_nonpos hb0,
    rw abs_of_nonpos,
    { ring},
    nlinarith,
  },
  { -- a ≤ 0 ≤ b
    rw abs_of_nonpos ha0,
    rw abs_of_nonneg h0b,
    rw abs_of_nonpos,
    { ring},
    nlinarith,
  },
  { -- both nonnegative
    rw abs_of_nonpos ha0,
    rw abs_of_nonpos hb0,
    rw abs_of_nonneg,
    { ring},
    nlinarith,
  },  
end

-- order level 6 (unfinished)
lemma le_iff_square_le (ha : 0 ≤ a) (hb : 0 ≤ b): a ≤ b ↔ a^2 ≤ b^2 :=
begin
  rw (show a^2 ≤ b^2 ↔ 0 ≤ b^2 - a^2, by split; intros; linarith),
  rw (show b^2 - a^2 = (b + a) * (b - a), by ring),
  rw (show a ≤ b ↔ 0 ≤ b - a, by split; intros; linarith), -- should be a lemma
  have hab : 0 ≤ b + a, by linarith,
  split,
  { intros,
    nlinarith},
  { intros,
    by_cases h : b + a = 0,
    { linarith },
    have ha2 : 0 < b + a,
    { by_contradiction hab,
      push_neg at hab,
      apply h,
      linarith
    },
    sorry
  } 
end


end test
