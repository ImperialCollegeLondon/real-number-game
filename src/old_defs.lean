import data.real.basic
import data.set.intervals
import tactic.norm_num

-- nonempty is a class but let's have it working on set ℝ

namespace real_number_game

-- hide (need to choose this or P)
class nonemptyT (S : set ℝ) : Type :=
(x : ℝ)
(thm : x ∈ S)

-- hide (need to choose this or T)
class nonemptyP (S : set ℝ) : Prop :=
(thm' : ∃ x : ℝ, x ∈ S)

def nonemptyP.thm (S : set ℝ) [nonemptyP S] :
  ∃ x : ℝ, x ∈ S :=
nonemptyP.thm'

-- irrelevant example
example : ∃ x: ℝ, x < 1 := ⟨0.5, by norm_num⟩
example : (0.5 : ℝ) < 1 := by norm_num

-- irrelevant example
noncomputable example : nonemptyT (set.Icc 0 1) :=
{ x := 0.5,
  thm := by {simp,split;norm_num}
}

-- show
def is_upper_bound (S : set ℝ) (b : ℝ) : Prop := ∀ s ∈ S, s ≤ b

-- hide this def
class bounded_aboveT (S : set ℝ) : Type :=
(b : ℝ) 
(thm : is_upper_bound S b)

-- hide this def
class bounded_aboveP (S : set ℝ) : Prop :=
(thm' : ∃ b : ℝ, is_upper_bound S b)

def bounded_aboveP.thm (S : set ℝ) [bounded_aboveP S] :
  ∃ b : ℝ, is_upper_bound S b :=
bounded_aboveP.thm'

-- example (for me only)
instance : bounded_aboveT (set.Icc 0 1) :=
{ b := 2,
  thm := λ r ⟨h1, h2⟩, le_trans h2 (by norm_num)
}

-- hide
noncomputable def Sup (S : set ℝ) [nonemptyP S] [bounded_aboveP S] := Sup S

-- state as axiom; hide proof
theorem le_Sup {S : set ℝ} [nonemptyP S] [bounded_aboveP S] : ∀ x ∈ S, x ≤ Sup S :=
begin
  apply real.le_Sup,
  cases bounded_aboveP.thm S with b hb,
  use b,
  exact hb,
end

-- state as axiom; hide proof
theorem Sup_le {S : set ℝ} [nonemptyP S] [bounded_aboveP S] :
  ∀ b : ℝ, is_upper_bound S b → Sup S ≤ b :=
begin
  intros b hb,
  show has_Sup.Sup S ≤ b,
  rw real.Sup_le,
  { exact hb},
  { cases nonemptyP.thm S with c hc, use c, exact hc},
  { use b, exact hb}
end

-- other axioms: ℤ unbounded, linearly ordered field.
-- Might need to introduce later.

end real_number_game 