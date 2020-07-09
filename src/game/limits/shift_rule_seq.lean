import game.limits.bounded_if_convergent

namespace xena
/- 
"Shift rule" for sequences, used in Series world:
-/

/- Lemma
Shift rule
-/


lemma shift_rule (a : ℕ → ℝ) (k : ℕ) (L : ℝ): 
     is_limit a L ↔ is_limit (λ (n : ℕ), a (n+k)) L :=

begin
split,
     {
     intro hlim,
     intros e he,
     unfold is_limit at hlim,
     specialize hlim e he, 
     cases hlim with N_1 hypN_1,
     use N_1,
     intros n hn,
     simp,
     have fact : N_1 ≤ n + k, linarith,
     specialize hypN_1 (n + k) fact,
     exact hypN_1,
     },

     {
     intro hlim,
     intros ε hε,
     unfold is_limit at hlim,
     specialize hlim ε hε, 
     cases hlim with N_2 hypN_2,
     use (k+ N_2),
     intros N hN,
     have fact : N_2 ≤ N - k, from nat.le_sub_left_of_add_le hN,  -- namespace issue here?
     specialize hypN_2 (N -k) fact,
     rw nat.sub_add_cancel at hypN_2, -- seems to need these nat. theorems
     exact hypN_2,
     linarith,
     }
     
end
end xena
