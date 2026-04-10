import CompPoly.Multivariate.CMvPolynomial

import Sumcheck.Src.Transcript
import Sumcheck.Src.Verifier
import Sumcheck.Properties.Events.BadTranscript
import Sumcheck.Properties.Models.Adversary
import Sumcheck.Properties.Models.AdversaryTranscript

def AcceptsEvent
  {𝔽} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (t : Transcript 𝔽 n) : Prop :=
  is_verifier_accepts_transcript (𝔽 := 𝔽) (n := n) domain p t = true

def AcceptsOnChallenges
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (domain : List 𝔽)
  (claim : 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (adv : Adversary 𝔽 n) :
  (Fin n → 𝔽) → Prop :=
fun r =>
  AcceptsEvent domain p (AdversaryTranscript claim p adv r)

def AcceptsAndBadTranscriptOnChallenges
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (domain : List 𝔽)
  (claim : 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (adversary : Adversary 𝔽 n) :
  (Fin n → 𝔽) → Prop :=
fun r =>
  AcceptsEvent domain p (AdversaryTranscript claim p adversary r)
  ∧ BadTranscriptEvent domain p (AdversaryTranscript claim p adversary r)
