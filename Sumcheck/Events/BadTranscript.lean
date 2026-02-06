import CompPoly.CMvPolynomial

import Sumcheck.Events.BadRound

import Sumcheck.Src.Transcript
import Sumcheck.Src.HonestProver
import Sumcheck.Src.Transcript

def BadTranscriptEvent
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽)
  (t : Transcript 𝔽 n) : Prop :=
  ∃ i : Fin n, BadRound (t.round_polys i) p t.challenges i
