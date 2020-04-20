import data.real.basic

/-
# Chapter 2 : Sup and Inf

## Level 9
-/


-- main result in lemma sup_mem_prod_of_sets
def mem_prod_sets (A : set ℝ) (B : set ℝ) := { x : ℝ | ∃ y ∈ A, ∃ z ∈ B, x = y * z}


/-
Intermediary result `zero_in_prod` proved in sets_level08.

Intermediary result `mem_prod_sets_lub_proof` in previous level.
-/


/- Lemma
For two non-empty sets of reals $A$ and $B$, it is not in general true that
$$ \textrm{sup} (A \cdot B) = \textrm{sup} (A) \cdot \textrm{sup}(B)$$
where $A \cdot B$ is defined pointwise as above.
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
