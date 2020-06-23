import game.order.max_API_test
import data.real.basic

noncomputable theory

namespace test

variables {a b c : ℝ}

-- What ℝ has that a general total order hasn't got, is - .

example : -a ≤ -b ↔ b ≤ a := by split; intros; linarith

def abs (x : ℝ) := max x (-x)

-- useful for rewriting
lemma abs_def (x : ℝ) : abs x = max x (-x) := rfl

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

theorem triangle : abs (a + b) ≤ abs a + abs b :=
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

theorem abs_mul : abs (a * b) = abs a * abs b :=
begin
  sorry
end


end test

