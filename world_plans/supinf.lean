import defs

instance : has_add (set ℝ) := ⟨λ S T, {u : ℝ | ∃ (s ∈ S) (t ∈ T), u = s + t}⟩

/-
Goal: state and prove Richard Thomas' problem sheet question. 
-/

namespace real_number_game

def is_nonempty (S : set ℝ) : Prop := ∃ s : ℝ, s ∈ S

def is_bounded_above (S : set ℝ) : Prop := ∃ b : ℝ, ∀ x ∈ S, x ≤ b

-- hide this from them
instance foo {S : set ℝ} [nonemptyP S] (x : ℝ) :
  nonemptyP {t : ℝ | ∃ s ∈ S, t = s + x} := ⟨
begin
  cases nonemptyP.thm S with s hs,
  use s + x,
  use s,
  use hs -- , refl
end⟩

-- they can do this
example (S : set ℝ) (hS : is_nonempty S) (x : ℝ) :
  is_nonempty {t : ℝ | ∃ s ∈ S, t = s + x} :=
begin
  cases hS with s hs,
  use s + x,
  use s,
  use hs, -- , refl
end

-- hide this from them
instance foo' {S : set ℝ} [bounded_aboveP S] (x : ℝ) :
  bounded_aboveP {t : ℝ | ∃ s ∈ S, t = s + x} := ⟨
begin
  cases bounded_aboveP.thm S with b hb,
  use b + x,
  intros t ht,
  rcases ht with ⟨s, hs, ht⟩,
  have hsb : s ≤ b,
    exact hb s hs,
  linarith,
end⟩

-- they can do this
example (S : set ℝ) (hs : is_bounded_above S) (x : ℝ) :
  is_bounded_above {t : ℝ | ∃ s ∈ S, t = s + x} :=
begin
  cases hs with b hb,
  use b + x,
  intros t ht,
  rcases ht with ⟨s, hs, ht⟩,
  have hsb : s ≤ b,
    exact hb s hs,
  linarith,
end

-- they can do this 
theorem Sup_add_real {S : set ℝ} [nonemptyP S] [bounded_aboveP S] (x : ℝ) :
Sup {t : ℝ | ∃ s ∈ S, t = s + x} = Sup S + x :=
begin
  apply le_antisymm,
  { apply Sup_le,
    intros t ht,
    rcases ht with ⟨s, hs, ht2⟩,
    have hs2 : s ≤ Sup S,
      exact le_Sup s hs,
    linarith,
  },
  { apply add_le_of_le_sub_right,
    apply Sup_le,
    intros s hs,
    apply le_sub_right_of_add_le,
    apply le_Sup,
    use s,
    use hs,
  }
end
-- theorems which need to be done.

-- theorem --THIS NEEDS TO BE TAUGHT. Don't need contradiction?
theorem exists_gt_of_lt_Sup (S : set ℝ) [nonemptyP S] [bounded_aboveP S] :
  ∀ c, c < Sup S → ∃ s ∈ S, c < s :=
begin
  intros c hc,
  apply classical.by_contradiction,
  intro h,
  push_neg at h,
  have h2 := Sup_le c h,
  linarith,
end

theorem gt_Sup_minus_eps (S : set ℝ) [nonemptyP S] [bounded_aboveP S] :
  ∀ ε, 0 < ε → ∃ s ∈ S, Sup S - ε < s :=
begin
  intros ε hε,
  apply exists_gt_of_lt_Sup,
  linarith,
end



-- too hard?
instance (X Y : set ℝ) [nonemptyT X] [nonemptyT Y] : nonemptyT (X + Y) :=
{ x := nonemptyT.x X + nonemptyT.x Y,
  thm := ⟨nonemptyT.x X, nonemptyT.thm X, nonemptyT.x Y, nonemptyT.thm Y, rfl⟩ 
}

-- too hard?
instance (X Y : set ℝ) [nonemptyP X] [nonemptyP Y] : nonemptyP (X + Y) :=
⟨ begin
    cases nonemptyP.thm X with a ha,
    cases nonemptyP.thm Y with b hb,
    use a + b,
    use a, use ha, use b, use hb,
  end⟩

-- What they can do:

theorem nonempty.add (X Y : set ℝ) (hX : is_nonempty X) (hY : is_nonempty Y) :
  is_nonempty (X + Y) :=
begin
  cases hX with a ha,
  cases hY with b hb,
  use a + b,
  use a, use ha, use b, use hb, -- no refl :-
end

-- too hard :-( without chat about instances
instance bounded_above.sum (X Y : set ℝ) [bounded_aboveT X] [bounded_aboveT Y] :
  bounded_aboveT (X + Y) :=
{ b := bounded_aboveT.b X + bounded_aboveT.b Y,
  thm := begin 
    rintro _ ⟨x, hx, y, hy, rfl⟩,
    have : x ≤ _ := bounded_aboveT.thm X x hx,
    have : y ≤ _ := bounded_aboveT.thm Y y hy,
    linarith
  end
}

instance bounded_aboveP.sum (X Y : set ℝ) [bounded_aboveP X] [bounded_aboveP Y] :
  bounded_aboveP (X + Y) :=
⟨ begin
    cases bounded_aboveP.thm X with a ha,
    cases bounded_aboveP.thm Y with b hb,
    use a + b,
    rintro _ ⟨x, hx, y, hy, rfl⟩,
    have : x ≤ a := ha x hx,
    have : y ≤ b := hb y hy,
    linarith
  end⟩

-- What they can do:

example (X Y : set ℝ) (hX : is_bounded_above X) (hY : is_bounded_above Y) : is_bounded_above (X + Y) :=
begin
  cases hX with a ha,
  cases hY with b hb,
  use a + b,
  intros z hz,
  rcases hz with ⟨x, hx, y, hy, h⟩,
  have h1 : x ≤ a := ha x hx,
  have h2 : y ≤ b := hb y hy,
  linarith,
end

-- Or maybe this?
def is_bounded_above_by (S : set ℝ) (b : ℝ) := ∀ s ∈ S, s ≤ b

example (X Y : set ℝ) (a b : ℝ) (haX : is_bounded_above_by X a) (hbY : is_bounded_above_by Y b) :
  is_bounded_above_by (X + Y) (a + b) :=
begin
  intros s hs,
  rcases hs with ⟨x, hx, y, hy, h⟩,
  have h1 : x ≤ a := haX x hx,
  have h2 : y ≤ b := hbY y hy,
  linarith,
end

-- theorem -- THIS NEEDS TO BE TAUGHT; this proof is *long*.
-- Probably should prove each direction separately
theorem real.Sup_add -- 
  (X : set ℝ) [h1X : nonemptyP X] [h2X : bounded_aboveP X]
  (Y : set ℝ) [h2Y : nonemptyP Y] [h2Y : bounded_aboveP Y] : 
  Sup (X + Y) = Sup X + Sup Y  :=
begin
  apply le_antisymm,
  {
    apply Sup_le,
    unfold is_upper_bound,
    intros s hs,
    rcases hs with ⟨x, hx, y, hy, h⟩,
    rw h,
    have h1 : x ≤ Sup X,
      exact le_Sup x hx,
    have h2 : y ≤ Sup Y,
      exact le_Sup y hy,
    linarith,
  },
  { by_contradiction h,
    push_neg at h,
    set ε := (Sup X + Sup Y) - Sup (X + Y) with hε,
    have h1 : 0 < ε/2,
      linarith,
    have h2 := gt_Sup_minus_eps X (ε/2) h1,
    have h3 := gt_Sup_minus_eps Y (ε/2) h1,
    rcases h2 with ⟨a, ha, h4⟩,
    rcases h3 with ⟨b, hb, h5⟩,
    have h6 : a + b ∈ X + Y,
      use a, use ha, use b, use hb,
    have h7 := le_Sup (a + b) h6,
    linarith,
  }
end 

-- now onto Richard Thomas' question about sup{sup(S1),sup(S2),sup(S3),...}=sup(union of S_i)

-- Hmm, we need a shedload of instances to make this make sense.
-- this is horrible, why not use ereal? If I used ereal then this is always true.

-- let me just start ploughing through this
instance foo3 (f : ℕ → set ℝ) (n : ℕ) [nonemptyP (f n)] : nonemptyP (⋃ i, f i) :=
⟨ begin
    cases nonemptyP.thm (f n) with x hx,
    use x,
    rw set.mem_Union,
    use n,
    assumption
  end⟩

-- still more typeclass issues with this. 
example (f : ℕ → set ℝ) [∀ n, nonemptyP (f n)]
  [bounded_aboveP (⋃ i, f i)] :
Sup (⋃ i, f i) = Sup (set.range (λ n, Sup (f n))) := sorry

end real_number_game

