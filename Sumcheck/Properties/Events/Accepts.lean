import CompPoly.Multivariate.CMvPolynomial

import Sumcheck.Src.Transcript
import Sumcheck.Src.Verifier
import Sumcheck.Properties.Events.BadTranscript

-- the verifier accepts a transcript
def AcceptsEvent
  {𝔽} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (t : Transcript 𝔽 n) : Prop :=
  is_verifier_accepts_transcript (𝔽 := 𝔽) (n := n) domain p t = true

-- the verifier accepts the prover's transcript for a given set of challenges
def AcceptsOnChallenges
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (st : SumcheckStatement 𝔽 n)
  (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n))) :
  (Fin n → 𝔽) → Prop :=
fun r =>
  AcceptsEvent st.domain st.polynomial (proverTranscript st P r)

-- the verifier accepts AND the transcript has a bad round
def AcceptsAndBadTranscriptOnChallenges
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (st : SumcheckStatement 𝔽 n)
  (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n))) :
  (Fin n → 𝔽) → Prop :=
fun r =>
  AcceptsEvent st.domain st.polynomial (proverTranscript st P r)
  ∧ BadTranscriptEvent st.domain st.polynomial (proverTranscript st P r)
