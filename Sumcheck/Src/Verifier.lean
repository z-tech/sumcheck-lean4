import CompPoly.CMvPolynomial

@[simp] def verifier_check {𝔽} [CommRing 𝔽] [DecidableEq 𝔽]
  (max_degree : ℕ)
  (round_claim : 𝔽)
  (round_p : CPoly.CMvPolynomial 1 𝔽) : Bool :=
  -- identity is sum over {0,1}
  let round_identity_ok : Prop :=
    CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (0 : 𝔽)) round_p +
    CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (1 : 𝔽)) round_p
      = round_claim
  let deg_bound_ok : Prop :=
    CPoly.CMvPolynomial.degreeOf ⟨0, by decide⟩ round_p ≤ max_degree
  decide round_identity_ok && decide deg_bound_ok

@[simp] def next_claim {𝔽} [CommRing 𝔽] [DecidableEq 𝔽]
  (round_challenge : 𝔽)
  (round_p : CPoly.CMvPolynomial 1 𝔽) : 𝔽 :=
  CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ => round_challenge) round_p
