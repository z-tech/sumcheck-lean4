import CompPoly.CMvPolynomial

@[simp] def verifier_check {𝔽} [CommRing 𝔽] [DecidableEq 𝔽]
  (round_claim : 𝔽)
  (round_p : CPoly.CMvPolynomial 1 𝔽) : Bool :=
  -- the round identity sum over {0,1}
  decide (
    CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ => 0) round_p +
    CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ => 1) round_p =
    round_claim
  )

@[simp] def next_claim {𝔽} [CommRing 𝔽] [DecidableEq 𝔽]
  (round_challenge : 𝔽)
  (round_p : CPoly.CMvPolynomial 1 𝔽) : 𝔽 :=
  CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ => round_challenge) round_p
