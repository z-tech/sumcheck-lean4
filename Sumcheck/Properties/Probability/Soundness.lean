import CompPoly.Multivariate.CMvPolynomial

import Sumcheck.Properties.Events.Accepts
import Sumcheck.Properties.Probability.Challenges

noncomputable def probSoundness
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (st : SumcheckStatement 𝔽 n)
  (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n))) : ℚ :=
  probEvent (E := AcceptsAndBadTranscriptOnChallenges st P)
