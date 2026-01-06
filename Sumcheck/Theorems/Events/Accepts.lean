import CompPoly.CMvPolynomial

import Sumcheck.Impl.Transcript
import Sumcheck.Impl.Reference.Transcript

def AcceptsEvent
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽)
  (t : Transcript 𝔽 n) : Prop :=
  is_accepting_transcript (𝔽 := 𝔽) (n := n) p t = true
