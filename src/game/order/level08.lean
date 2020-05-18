import data.real.basic
import data.real.irrational

open real

namespace xena -- hide

/-
# Chapter 2 : Order

## Level 8

Prove by example that there exist pairs of real numbers
$a$ and $b$ such that $a \in \mathbb{R} \setminus \mathbb{Q}$, 
$b \in \mathbb{R} \setminus \mathbb{Q}$,
but their product $a \cdot b$ is a rational number, $(a \cdot b) \in \mathbb{Q}$.
You may use this result in the Lean mathlib library:

`irrational_sqrt_two : irrational (sqrt 2)
-/


/- Lemma
Not true that for any $a$, $b$, irrational numbers, the product is 
also an irrational number.
-/
theorem not_prod_irrational : 
    ¬ ( ∀ (a b : ℝ), irrational a →  irrational b → irrational (a*b) ) :=
begin
  intro H,
  have H2 := H (sqrt 2) (sqrt 2),
  have H3 := H2 irrational_sqrt_two irrational_sqrt_two,
  apply H3,
  existsi (2 : ℚ),
  simp, norm_num, done
end

end xena -- hide
