lemma L1 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : a^2 = b^2 → a = b :=
begin
    intro H,
    have A : sqrt (a ^ 2) = sqrt (a ^ 2), refl,
    rw H at A {occs := occurrences.pos [2]},
    have G := sqrt_sqr ha, rw G at A,
    have F := sqrt_sqr hb, rw F at A, 
    exact A, done
end