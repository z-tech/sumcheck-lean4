import CompPoly.Multivariate.CMvPolynomial

def Adversary (𝔽 : Type _) (n : ℕ) [CommRing 𝔽] :=
  ∀ (_p : CPoly.CMvPolynomial n 𝔽) (_claim : 𝔽),
    ∀ i : Fin n, (Fin i.val → 𝔽) → CPoly.CMvPolynomial 1 𝔽
