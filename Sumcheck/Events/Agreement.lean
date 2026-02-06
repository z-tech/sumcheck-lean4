import CompPoly
import CompPoly.CMvPolynomial
import CompPoly.CMvMonomial
import CompPoly.Lawful

import Sumcheck.Src.Verifier

def AgreementEvent
  {n} {𝔽} [CommRing 𝔽]
  (g h : CPoly.CMvPolynomial n 𝔽) : (Fin n → 𝔽) → Prop :=
  fun a => CPoly.CMvPolynomial.eval a g = CPoly.CMvPolynomial.eval a h

instance agreementEvent_decidable
  {n : ℕ} {𝔽} [CommRing 𝔽] [DecidableEq 𝔽]
  (g h : CPoly.CMvPolynomial n 𝔽) :
  DecidablePred (AgreementEvent g h) := by
  intro a
  dsimp [AgreementEvent]
  infer_instance

@[simp] lemma AgreementEvent_eval_equiv
  {n : ℕ} {𝔽 : Type _} [CommRing 𝔽]
  (g h : CPoly.CMvPolynomial n 𝔽) (a : Fin n → 𝔽) :
  AgreementEvent g h a
    ↔ (MvPolynomial.eval a) (CPoly.fromCMvPolynomial g)
        = (MvPolynomial.eval a) (CPoly.fromCMvPolynomial h) := by
  simp [AgreementEvent, CPoly.eval_equiv]

abbrev AgreementAtEvent {n} {𝔽} [CommRing 𝔽] (g h : CPoly.CMvPolynomial n 𝔽) (assignment : Fin n → 𝔽) : Prop :=
  AgreementEvent g h assignment
