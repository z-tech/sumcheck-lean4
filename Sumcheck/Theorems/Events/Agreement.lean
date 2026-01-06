import CompPoly.CMvPolynomial

import Sumcheck.Impl.Reference.Verifier

def AgreementEvent
  {n} {𝔽} [CommRing 𝔽]
  (g h : CPoly.CMvPolynomial n 𝔽) : (Fin n → 𝔽) → Prop :=
  fun a => CPoly.CMvPolynomial.eval a g = CPoly.CMvPolynomial.eval a h

abbrev AgreementAt {n} {𝔽} [CommRing 𝔽] (g h : CPoly.CMvPolynomial n 𝔽) (assignment : Fin n → 𝔽) : Prop :=
  AgreementEvent g h assignment

def AgreementNextClaimEvent
  {𝔽} [CommRing 𝔽] [DecidableEq 𝔽]
  (g h : CPoly.CMvPolynomial 1 𝔽) : 𝔽 → Prop :=
  fun r => next_claim r g = next_claim r h
