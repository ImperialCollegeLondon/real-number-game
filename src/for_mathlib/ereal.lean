import data.real.basic 




/-- ereal : The set $$[-\infty,+\infty]$$ -/

def ereal := with_bot (with_top ℝ)

instance : linear_order ereal := 
by unfold ereal; apply_instance
instance : lattice.has_top ereal := 
by unfold ereal; apply_instance
instance : lattice.has_bot ereal :=
by -- guess what
unfold ereal; apply_instance
instance : has_zero ereal := by unfold ereal; apply_instance instance : lattice.order_bot ereal := by unfold ereal; apply_instance


--example (Roo : Type) : set (with_bot Roo) → set (Roo) := λ (f : with_bot Roo )
--#print is_lub -- is_least (upper_bounds X)

local attribute [instance, priority 10] classical.prop_decidable
def has_Sup (X : set ereal) : Prop := ∃ l : ereal, is_lub X l

def Sup_exists (X : set ereal) : has_Sup X :=
begin
  let Xoc : set (with_top ℝ) := λ x, X (↑x : with_bot _),
  exact dite (Xoc = ∅) (λ h, begin
    use ⊥,
    split,
    { intros x hx,
      cases x, exact le_refl none,
      exfalso,
      apply set.not_mem_empty x,
      rw ←h,
      exact hx,
    },
    intros u hu,
    exact lattice.bot_le,
  end) (λ h, begin
    let Xoo : set ℝ := λ (x : ℝ), Xoc (↑ x), 
    by_cases h2 : nonempty (upper_bounds Xoo),
    { use (↑(↑(real.Sup Xoo : real) : with_top ℝ) : with_bot (with_top ℝ)),
      sorry
    },
    sorry,
  end)
--  if (λ (x : with_top ℝ), X x) = (∅ : set (with_top ℝ)) then sorry else sorry,
end



#exit




/-- The set $$[-\infty,+\infty]$$ is a
<a href="https://en.wikipedia.org/wiki/Complete_lattice">complete lattice.</a> -/
noncomputable instance : lattice.complete_lattice (ereal) :=
{ top := ⊤,
  le_top := λ _, lattice.le_top,
  bot := ⊥,
  bot_le := @lattice.bot_le _ _,
  Sup := begin sorry end,--λ X, if X ⊆ {⊥} then ⊥ else sorry,
  Inf := λ X, ⊥,
  le_Sup := _,
  Sup_le := _,
  Inf_le := sorry,
  le_Inf := sorry,
  ..with_bot.lattice }

-- what is ⁇?