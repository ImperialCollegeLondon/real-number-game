import data.real.basic

/-
# Chapter 3 : Sup and Inf

## Level 5

A classical result: the supremum of an element-wise sum of sets.
-/

-- see also ds_infSum.lean for only the better-organized version -- hide
def sum_of_sets (A : set ℝ) (B : set ℝ) := { x : ℝ | ∃ y ∈ A, ∃ z ∈ B, x = y + z}

/- Lemma
If $A$ and $B$ are sets of reals, then
$$ \textrm{sup} (A + B) = \textrm{sup} (A) + \textrm{sup}(B)$$
-/
lemma sup_sum_of_sets (A : set ℝ) (B : set ℝ) (h1A : A.nonempty) (h1B : B.nonempty) 
  (h2A : bdd_above A) (h2B : bdd_above B) (a : ℝ) (b : ℝ) : 
  (is_lub A a) ∧ (is_lub B b) → is_lub (sum_of_sets A B) (a + b) :=
begin
  intro h,
  cases h with hA hB,
  split,
  { -- prove that (a+b) is an upper bound
    intros x h0,
    cases h0 with y h1, cases h1 with yA h2,
    cases h2 with z h3, cases h3 with zB hx,
    have H12A := hA.left, have H12B := hB.left,
    have H13A := H12A yA, have H13B := H12B zB,
    linarith,
  },
  -- now prove that (a+b) is the least upper bound
  intros S hS,
  --change ∀ xab ∈ (sum_of_sets A B), xab ≤ S at hS,
  have H1 : ∀ y ∈ A, ∀ z ∈ B, (y + z) ∈ (sum_of_sets A B),
    intros y hy z hz,
    unfold sum_of_sets, 
    existsi y, existsi hy, existsi z, existsi hz, refl,
  have H2 : ∀ y ∈ A, ∀ z ∈ B, (y + z) ≤ S, 
    intros y hy z hz,
    apply hS, exact H1 y hy z hz,
  have H3 : ∀ y ∈ A, ∀ z ∈ B, y ≤ S - z,
    intros y hy z hz,
    have H3a := H2 y hy z hz,
    exact le_sub_right_of_add_le H3a,
  have h21B := hB.right, have h22B := hB.left,
  --change ∀ z ∈ B, z ≤ b at h22B,
  have H4 : ∀ z ∈ B, (S - z) ∈ upper_bounds A, --!
    intros z hz y hy,
    exact H3 y hy z hz,
  have H5 : ∀ z ∈ B, a ≤ (S - z), 
    intros z hz,
    have H13A := hA.right,
    change ∀ u ∈ upper_bounds A, a ≤ u at H13A,
    have H5a := H4 z hz, 
    exact H13A (S-z) H5a,
  have H6 : ∀ z ∈ B, z ≤ S - a,
    intros z hz,
    have H6a := H5 z hz, exact le_sub.1 H6a,
  --have H7 : (S - a) ∈ upper_bounds B, exact H6,
  have H8 : b ≤ (S-a),
    have H13B := hB.right,
    change ∀ u ∈ upper_bounds B, b ≤ u at H13B,
    exact H13B (S-a) H6,  -- I had H7 instead of H6 here
  exact add_le_of_le_sub_left H8, done
end

-- Kevin's term proof for second part
lemma sup_sum_of_sets' (A : set ℝ) (B : set ℝ) (a : ℝ) (b : ℝ)
  (hA : is_lub A a) (hB : is_lub B b) :
  a + b ∈ lower_bounds (upper_bounds (sum_of_sets A B)) :=
    λ S hS, add_le_of_le_sub_left $ hB.2 $ λ z hz, le_sub.1 $ hA.2 $ λ y hy, 
    le_sub_right_of_add_le $ hS ⟨y, hy, z, hz, rfl⟩

-- Patrick Massot's proof for second part
lemma sup_sum_of_sets'' (A : set ℝ) (B : set ℝ) (a : ℝ) (b : ℝ)
  (hA : is_lub A a) (hB : is_lub B b) :
  a + b ∈ lower_bounds (upper_bounds (sum_of_sets A B)) :=
begin
    intros S hS,
  have H1 : ∀ x ∈ A, S - x ∈ upper_bounds B,
  { intros x hx y hy,
    suffices : x + y ≤ S, by linarith, -- by rwa le_sub_iff_add_le',
    exact hS ⟨x, hx, y, hy, rfl⟩, },
  have H2 : S - b ∈ upper_bounds A,
  { intros x hx,
    suffices : b ≤ S - x, by linarith, -- by rwa le_sub,
    exact hB.2 (H1 x hx) },
  linarith [hA.2 H2],  --exact le_sub_iff_add_le.mp (hA.2 H2),
end
