import data.real.basic
import data.set.intervals
import tactic.norm_num

-- nonempty is a class but let's have it working on set ℝ

namespace real_number_game

-- hide
class nonempty (S : set ℝ) : Type :=
(x : ℝ)
(thm : x ∈ S)

example : ∃ x: ℝ, x < 1 := ⟨0.5, by norm_num⟩
example : (0.5 : ℝ) < 1 := by norm_num

-- example
noncomputable example : nonempty (set.Icc 0 1) :=
{ x := 0.5,
  thm := ⟨by unfold algebra.div;norm_num,by unfold algebra.div;norm_num⟩
}

-- show
def is_upper_bound (S : set ℝ) (b : ℝ) : Prop := ∀ s ∈ S, s ≤ b

-- hide
class bounded_above (S : set ℝ) : Type :=
(b : ℝ) 
(thm : is_upper_bound S b)

-- example (for me only)
instance : bounded_above (set.Icc 0 1) :=
{ b := 2,
  thm := λ r ⟨h1, h2⟩, le_trans h2 (by norm_num)
}

-- hide
noncomputable def Sup (S : set ℝ) [nonempty S] [bounded_above S] := real.Sup S

-- axiom; hide proof
theorem le_Sup {S : set ℝ} [nonempty S] [bounded_above S] : ∀ x ∈ S, x ≤ Sup S :=
begin
  apply real.le_Sup,
  use bounded_above.b S,
  exact bounded_above.thm S,
end

-- axiom; hide proof
theorem Sup_le {S : set ℝ} [nonempty S] [bounded_above S] : ∀ b : ℝ, is_upper_bound S b → Sup S ≤ b :=
begin
  intros b hb,
  show real.Sup S ≤ _,
  rw real.Sup_le,
  { exact hb},
  { use nonempty.x S, exact nonempty.thm S},
  { use b, exact hb}
end




end real_number_game 