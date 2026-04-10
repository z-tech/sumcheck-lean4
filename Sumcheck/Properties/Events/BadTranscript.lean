import CompPoly.Multivariate.CMvPolynomial

import Sumcheck.Properties.Events.BadRound

import Sumcheck.Src.Transcript
import Sumcheck.Src.Prover

def BadTranscriptEvent
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (t : Transcript 𝔽 n) : Prop :=
  ∃ i : Fin n, BadRound domain (t.round_polys i) p t.challenges i
