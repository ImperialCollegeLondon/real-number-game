import data.real.basic
local attribute [instance] classical.prop_decidable

-- to be technically correct, the definition below should include 
-- a hypothesis that for ε > 0
-- but that does raise some issues which I don't know how to handle
-- when using it in the lemma
def neighborhood (a : ℝ) (ε : ℝ) := { x : ℝ | abs(a - x) < ε} 
def neighborhood1 (a : ℝ) (ε : ℝ) (h : ε > 0) := { x : ℝ | abs(a - x) < ε}
lemma hausdorff_reals (a b : ℝ) (hne : a ≠ b) : 
  ∃ (ε:ℝ), ε > 0 ∧ (neighborhood a ε ∩ neighborhood b ε = ∅) :=
begin
  set d := abs(b-a) with hd,
  have h1 : 0 < d, 
    rw hd, by_contradiction hf, push_neg at hf, 
    have h11 := abs_nonneg (b-a),
    have h12 : abs(b-a) = 0, linarith,
    have h13 : (b-a) = 0, exact abs_eq_zero.1 h12,
    have h14 : a = b, linarith, 
    exact hne h14,
  set e := d / 3 with he,
  use e, split, linarith,
  by_contradiction H,
  -- the stuff below can probably be made much shorter
  have G := set.ne_empty_iff_nonempty.mp H,
  cases G with x hab, cases hab with ha hb,
  have ha1 : abs(a-x) < e, exact ha,  -- linarith below won't work
  have hb1 : abs(b-x) < e, exact hb,  -- without these
  have hb2 : abs(b-x) = abs(x-b), exact abs_sub _ _,
  rw hb2 at hb1,
  have hab := abs_add (a-x) (x-b), 
  have hab1 : a - x + (x - b) = a - b, ring,
  rw hab1 at hab,
  have hab2 : abs(a-b) <  e + e, linarith,
  have hdd : d = 3 * e, rw he, linarith,
  rw hdd at hd, 
  have hde := eq.symm hd, 
  have hdf : abs(b-a) > 2 * e,
    linarith,
  have hdg : e + e = 2 * e, linarith,
  rw hdg at hab2, 
  have hb2 : abs(b-a) = abs(a-b), exact abs_sub _ _,
  rw hb2 at hdf, linarith, done
end
