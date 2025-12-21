import CompPoly.CMvPolynomial

@[simp]
def eval_at {𝔽} [CommRing 𝔽] (x : 𝔽) (p : CPoly.CMvPolynomial 1 𝔽) : 𝔽 :=
  CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ => x) p
