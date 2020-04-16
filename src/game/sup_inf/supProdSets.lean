import data.real.basic

-- main result in lemma sup_mem_prod_of_sets
def mem_prod_sets (A : set ℝ) (B : set ℝ) := { x : ℝ | ∃ y ∈ A, ∃ z ∈ B, x = y * z}


/-
The next two results go in the sidebar!
-/

--intermediary result
lemma zero_in_prod : (0:ℝ) ∈ mem_prod_sets (set.Icc (-2) (-1)) (set.Icc (0:ℝ) 3) :=
begin
  set a0 := (0:ℝ) with ha,
  have h1 : a0 ∈ (set.Icc (0:ℝ) 3), simp, linarith,
  set b := (-2:ℝ) with hb,
  have h2 : b ∈ set.Icc (-2:ℝ) (-1:ℝ), simp, linarith,
  use b, split, exact h2,
  use a0, split, exact h1, rw ha, norm_num, done
end

-- intermediary result
lemma mem_prod_sets_lub_proof : 
  is_lub (mem_prod_sets (set.Icc (-2:ℝ) (-1:ℝ)) (set.Icc (0:ℝ) (3:ℝ)) ) 0 := 
begin
  split,
  intros x h1,
  cases h1 with a hh, cases hh with ha h2,
  cases h2 with b h3, cases h3 with hb hx,
  have H : a ≤ 0, 
    cases ha with hg hl,
    linarith,
  have G : b ≥ 0, 
    cases hb with hg hl, exact hg,
  rw hx, exact mul_nonpos_of_nonpos_of_nonneg H G,
  intros x hx,
  by_contradiction hnx,
  push_neg at hnx,
  have E := zero_in_prod,
  have D := hx E, linarith, done
end

/- Lemma
For two non-empty sets of reals $A$ and $B$, it is not in general true that
$$ \textrm{sup} (A \cdot B) = \textrm{sup} (A) \cdot \textrm{sup}(B)$$
where $A \cdot B is defined pointwise as above.
-/
lemma sup_mem_prod_of_sets : ¬ ( ∀ (A B : set ℝ) (a b : ℝ),
  A.nonempty ∧ B.nonempty → bdd_below A ∧ bdd_below B →
  is_lub A a ∧ is_lub B b → 
  is_lub (mem_prod_sets A B) (a * b) ) :=
begin
  intro H,
  -- do an example with A = [-2,-1], B = [0,3]
  set A1 : set ℝ := set.Icc (-2:ℝ) (-1:ℝ) with hA,
  set B1 : set ℝ := set.Icc (0:ℝ) (3:ℝ) with hB,
  set a : ℝ := (-1:ℝ) with ha,
  set b : ℝ := (3 : ℝ) with hb,
  have G := H A1 B1,
  have h1A : A1.nonempty, simp, norm_num,
  have h1B : B1.nonempty, simp, norm_num,
  have F := G a b (and.intro h1A h1B),
  have h11 : ((-2:ℝ) ≤ -1), norm_num,
  have h21 : (0:ℝ) ≤ (3:ℝ), norm_num,
  have h2A : bdd_below A1, 
    -- use the definition in bounds.lean
    have h12 := is_glb_Icc h11,
    cases h12 with hh hhh,
    existsi (-2:ℝ), exact hh,
  have h2B : bdd_below B1, 
    have h22 := is_glb_Icc h21,
    cases h22 with hh hhh,
    existsi (0:ℝ), exact hh,
  have E := F (and.intro h2A h2B),
  have h1 : is_lub A1 a, 
    exact is_lub_Icc h11,
  have h2 : is_lub B1 b, 
    exact is_lub_Icc h21,
  have D := E (and.intro h1 h2),
  rw ha at h1, rw hb at h2, rw ha at D, rw hb at D,
  have E : is_lub (mem_prod_sets A1 B1) 0, 
    exact mem_prod_sets_lub_proof,
  have E1 := is_lub.unique D E,
  linarith, done
end
