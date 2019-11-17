import data.real.basic 

/-- ereal : The type $$[-\infty,+\infty]$$ -/
def ereal := with_bot (with_top ℝ)

instance : linear_order ereal := 
by unfold ereal; apply_instance
instance : lattice.has_top ereal := 
by unfold ereal; apply_instance
instance : lattice.has_bot ereal :=
by -- guess what
unfold ereal; apply_instance
instance : has_zero ereal := by unfold ereal; apply_instance instance : lattice.order_bot ereal := by unfold ereal; apply_instance instance : lattice.order_top ereal := by unfold ereal; apply_instance

def ereal.neg : ereal → ereal
| none := ⊤
| (some none) := ⊥
| (some (some x)) := ((↑-x : with_top ℝ) : with_bot (with_top ℝ))

instance : has_neg ereal := ⟨ereal.neg⟩

def ereal.neg_le_of : ∀ (a b : ereal) (h : -a ≤ b), -b ≤ a
| none none h := by cases (lattice.le_bot_iff.1 h)
| none (some b) h := by cases (lattice.top_le_iff.1 h); exact le_refl _
| (some none) b h := lattice.le_top
| (some (some a)) none h := by cases (lattice.le_bot_iff.1 h)
| (some (some a)) (some none) h := lattice.bot_le
| (some (some a)) (some (some b)) h := 
begin
  revert h,
  change (((-a : ℝ) : with_top ℝ) : with_bot (with_top ℝ)) ≤ _ →
    (((-b : ℝ) : with_top ℝ) : with_bot (with_top ℝ)) ≤ _,
  unfold_coes, simpa using neg_le_of_neg_le,
end

def ereal.neg_le {a b : ereal} : -a ≤ b ↔ -b ≤ a := ⟨ereal.neg_le_of a b, ereal.neg_le_of b a⟩

def ereal.neg_neg : ∀ (a : ereal), - (- a) = a
| none := rfl
| (some none) := rfl
| (some (some a)) := show (((- -a : ℝ) : with_top ℝ) : with_bot (with_top ℝ)) = (((a : ℝ) : with_top ℝ) : with_bot (with_top ℝ)),
by simp [neg_neg a]

def ereal.le_neg_of (a b : ereal) (h : a ≤ -b) : b ≤ -a :=
by rwa [←ereal.neg_neg b, ereal.neg_le, ereal.neg_neg]

def has_Sup (X : set ereal) : Prop := ∃ l : ereal, is_lub X l

local attribute [instance, priority 10] classical.prop_decidable

def Sup_exists (X : set ereal) : has_Sup X :=
begin
  let Xoc : set (with_top ℝ) := λ x, X (↑x : with_bot _),
  exact dite (Xoc = ∅) (λ h, ⟨⊥, begin
    split,
    { rintro (⟨⟩|x) hx, exact le_refl none,
      exfalso,
      apply set.not_mem_empty x,
      rw ←h,
      exact hx,
    },
    { intros u hu,
      exact lattice.bot_le}
  end⟩) (λ h, dite (⊤ ∈ Xoc) (λ h2, ⟨⊤, begin
    split, intros x hx, exact lattice.le_top,
    intros x hx,
    apply hx,
    exact h2,
  end⟩) begin
    intro htop,
    let Xoo : set ℝ := λ (x : ℝ), Xoc (↑ x),
    by_cases h2 : nonempty (upper_bounds Xoo),
    { rcases h2 with ⟨b, hb⟩,
      use (↑(↑(real.Sup Xoo : real) : with_top ℝ) : with_bot (with_top ℝ)),
      split,
      { intros x hx,
        cases x, exact lattice.bot_le,
        change (↑x : with_bot (with_top ℝ)) ≤ _,
        change x ∈ Xoc at hx,
        cases x with x, exact false.elim (htop hx),
        change (↑(↑x : with_top ℝ) : with_bot (with_top ℝ)) ≤ _,
        change x ∈ Xoo at hx,
        have h3 : x ≤ real.Sup Xoo,
          apply real.le_Sup,
          { use b,
            exact hb,
          },
        { exact hx},
          simp [h3],
        },
      { intros c hc,
        cases c with c,
          exfalso,
          replace h : ∃ x : with_top ℝ, x ∈ Xoc,
            apply classical.by_contradiction,
            intro h4, apply h,
            ext x,
            split, swap, intro h, cases h,
            intro hx,
            exfalso, apply h4,
            use x, assumption,
          cases h with x hx,
          replace hc := hc (↑x : with_bot _) hx,
          replace hc := lattice.le_bot_iff.1 hc,
          cases hc,
        change (↑c : with_bot _) ∈ _ at hc,
        cases c with c,
          unfold_coes, simp,
          suffices : real.Sup Xoo ≤ c,
            unfold_coes, simp [this],
          refine (real.Sup_le Xoo _ _).2 _,
          apply classical.by_contradiction,
            intro h2,
            apply h,
            ext x,
            split, swap, rintro ⟨⟩,
            intro h3,
            cases x with x, exfalso, apply htop, exact h3,
            exfalso, apply h2, use x, exact h3,
          use b,
          exact hb,
        intros x hx,
        replace hc := hc (↑(↑x : with_top ℝ) : with_bot (with_top ℝ)) hx,
        unfold_coes at hc,
        simpa using hc,
      }
    },
    { use ⊤,
      split, intros x hx, exact lattice.le_top,
      intros b hb,
      rw lattice.top_le_iff,
      cases b with b,
        exfalso,
        apply h,
        ext x,
        split, swap, rintro ⟨⟩,
        intro hx,
        exfalso,
        replace hb : ↑x ≤ ⊥ := hb (↑x : with_bot _) hx,
        rw lattice.le_bot_iff at hb,
        cases hb,
      cases b with b, refl,
      exfalso,
      apply h2,
      use b,
      intros x hx,
      replace hb := hb (↑(↑x : with_top ℝ) : with_bot (with_top ℝ)) hx,
      unfold_coes at hb,
      simpa using hb,
    }
  end) 
end

noncomputable def ereal.Sup := λ X, classical.some (Sup_exists X)

noncomputable instance : lattice.has_Sup ereal := ⟨ereal.Sup⟩

/-- The set $$[-\infty,+\infty]$$ is a
<a href="https://en.wikipedia.org/wiki/Complete_lattice">complete lattice.</a> -/
noncomputable instance : lattice.complete_lattice (ereal) :=
{ top := ⊤,
  le_top := λ _, lattice.le_top,
  bot := ⊥,
  bot_le := @lattice.bot_le _ _,
  Sup := ereal.Sup,
  Inf := λ X, -classical.some (Sup_exists ({mx | ∃ x ∈ X, mx = -x})),
  le_Sup := begin
    intros X x hx,
    have h := classical.some_spec (Sup_exists X),
    exact h.1 _ hx,
  end,
  Sup_le := begin
    intros X b hb,
    have h := classical.some_spec (Sup_exists X),
    cases h with h1 h2,
    change ereal.Sup X ∈ _ at h2,
    apply h2,
    exact hb,
  end,
  Inf_le := begin
    intros X x hx,
    have h := classical.some_spec (Sup_exists ({mx | ∃ x ∈ X, mx = -x})),
    rw ←ereal.neg_le,
    apply h.1,
    use x, use hx,
  end,
  le_Inf := begin
    intros X b hb,
    have h := classical.some_spec (Sup_exists ({mx | ∃ x ∈ X, mx = -x})),
    cases h with h1 h2,
    change ereal.Sup {mx | ∃ x ∈ X, mx = -x} ∈ _ at h2,
    apply ereal.le_neg_of,
    apply h2,
    intros mx hmx,
    apply ereal.le_neg_of,
    apply hb,
    rcases hmx with ⟨x, hx, hmx⟩,
    rw hmx,
    rwa ereal.neg_neg,
  end,
  ..with_bot.lattice }
