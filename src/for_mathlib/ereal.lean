import data.real.basic 




/-- ereal : The set $$[-\infty,+\infty]$$ -/

def ereal := with_bot (with_top ℝ)

/-- The set $$[-\infty,+\infty]$$ is a
<a href="https://en.wikipedia.org/wiki/Complete_lattice">complete lattice.</a> -/
noncomputable instance : lattice.complete_lattice (with_bot (with_top ℝ)) :=
{ top := ⊤,
  le_top := @lattice.le_top _ _,
  bot := ⊥,
  bot_le := @lattice.bot_le _ _,
  Sup := λ X, if X ⊆ {⊥} then ⊥ else sorry,
  Inf := λ X, ⊥,
  le_Sup := by rintros; simp,
  Sup_le := _,
  Inf_le := sorry,
  le_Inf := sorry,
  ..with_bot.lattice }

-- what is ⁇?