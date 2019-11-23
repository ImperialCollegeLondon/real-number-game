import defs

instance : has_add (set ℝ) := ⟨λ S T, {u : ℝ | ∃ (s ∈ S) (t ∈ T), u = s + t}⟩

/-
Goal : prove the following theorem.

Sup(X+Y)=Sup(X)+Sup(Y).
Goal after that: state and prove Richard Thomas' problem sheet question. 
-/

namespace real_number_game

-- theorem --THIS NEEDS TO BE TAUGHT 
theorem gt_Sup_minus_eps (S : set ℝ) [nonempty S] [bounded_above S] :
  ∀ ε, 0 < ε → ∃ s ∈ S, Sup S - ε < s :=
begin
  intros ε hε,
  apply classical.by_contradiction,
  intro h,
  push_neg at h,
  have h2 := Sup_le (Sup S - ε) h,
  linarith,
end

-- too hard?
instance (X Y : set ℝ) [nonempty X] [nonempty Y] : nonempty (X + Y) :=
{ x := nonempty.x X + nonempty.x Y,
  thm := ⟨nonempty.x X, nonempty.thm X, nonempty.x Y, nonempty.thm Y, rfl⟩ 
}

-- too hard :-( without lectures about instances
instance bounded_above.sum (X Y : set ℝ) [bounded_above X] [bounded_above Y] : bounded_above (X + Y) :=
{ b := bounded_above.b X + bounded_above.b Y,
  thm := begin 
    rintro _ ⟨x, hx, y, hy, rfl⟩,
    have : x ≤ _ := bounded_above.thm X x hx,
    have : y ≤ _ := bounded_above.thm Y y hy,
    linarith
  end
}

-- What they can do:
def is_bounded_above (S : set ℝ) : Prop := ∃ b : ℝ, ∀ x ∈ S, x ≤ b

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



theorem real.Sup_add -- or is it real.Sup.add?
  (X : set ℝ) [h1X : nonempty X] [h2X : bounded_above X]
  (Y : set ℝ) [h2Y : nonempty Y] [h2Y : bounded_above Y] : 
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

end real_number_game

/-
Maths proof.
First claim that X+Y is non-empty and bounded above. 
Now need to show (1) Sup(X+Y)<=Sup(X)+Sup(Y) and (2) Sup(X)+Sup(Y)<=Sup(X+Y)

(1) 
    stp Sup(X)+Sup(Y) is an upper bound by def of Sup
    x+y<=Sup(X)+Sup(Y) because x<=Sup(X) and y<=Sup(Y) and linarith

(2) 
    Need that if S is non-empty and bounded above, then
      for all ε > 0, there's s in S with s>Sup(S)-ε
    
    By contradiction. 
    Suppose Sup(X+Y)<sup(X)+sup(Y)




-/