import CompPoly.CMvPolynomial

import Sumcheck.Impl.Transcript
import Sumcheck.Impl.HonestTranscript
import Sumcheck.Events.BadTranscript
import Sumcheck.Models.Adversary
import Sumcheck.Models.AdversaryTranscript

def AcceptsEvent
  {𝔽} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽)
  (t : Transcript 𝔽 n) : Prop :=
  is_verifier_accepts_transcript (𝔽 := 𝔽) (n := n) p t = true

def AcceptsAndBadOnChallenges
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (claim : 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (adversary : Adversary 𝔽 n) :
  (Fin n → 𝔽) → Prop :=
fun r =>
  AcceptsEvent p (AdversaryTranscript claim p adversary r)
  ∧ BadTranscriptEvent p (AdversaryTranscript claim p adversary r)
