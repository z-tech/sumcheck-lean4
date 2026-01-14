import CompPoly.CMvPolynomial

structure Transcript (𝔽 : Type _) (n : ℕ) [CommRing 𝔽] where
  round_polys : Fin n → (CPoly.CMvPolynomial 1 𝔽)
  challenges : Fin n → 𝔽
  claims : Fin (n + 1) → 𝔽
