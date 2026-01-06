import CompPoly.CMvPolynomial

abbrev all_assignments_n (n : ℕ) (𝔽 : Type _) [Fintype 𝔽] : Finset (Fin n → 𝔽) :=
  (Finset.univ : Finset (Fin n → 𝔽))
