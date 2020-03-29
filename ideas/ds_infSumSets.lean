import data.real.basic

-- the better-organized version of the proof
def sum_of_sets (A : set ℝ) (B : set ℝ) := { x : ℝ | ∃ y ∈ A, ∃ z ∈ B, x = y + z}
lemma inf_sum_of_sets (A : set ℝ) (B : set ℝ) (h1A : A.nonempty) (h1B : B.nonempty) 
  (h2A : bdd_below A) (h2B : bdd_below B) (a : ℝ) (b : ℝ) : 
  (is_glb A a) ∧ (is_glb B b) → is_glb (sum_of_sets A B) (a + b) :=
begin
  intro h,
  cases h with hA hB,
  split,
  -- prove that (a+b) is a lower bound
  intros x h0,
  cases h0 with y h1,
  cases h1 with yA h2,
  cases h2 with z h3,
  cases h3 with zB hx,
  --have H11A := hA.right, have H11B := hB.right,
  have H12A := hA.left, have H12B := hB.left,
  have H13A := H12A yA, have H13B := H12B zB,
  linarith,
  -- now prove (a+b) is the greatest lower bound
  intros L hL,  -- L is another lower bound of (A+B)
  have H1 : ∀ x ∈ A, (L - x) ∈ lower_bounds B,
  { 
    intros x hx y hy, 
    suffices : L ≤ x + y, by linarith,
    exact hL ⟨x, hx, y, hy, rfl⟩,
  },
  have H2 : L - b ∈ lower_bounds A,
  { 
    intros x hx, 
    suffices : L - x ≤ b, by linarith,
    exact hB.2 (H1 x hx),
  },
  linarith [hA.2 H2], done
end
