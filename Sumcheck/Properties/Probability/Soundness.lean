import CompPoly.Multivariate.CMvPolynomial

import Sumcheck.Properties.Events.Accepts
import Sumcheck.Properties.Probability.Challenges

noncomputable def prob_soundness
  {𝔽 n} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (domain : List 𝔽)
  (claim : 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (adv : Adversary 𝔽 n) : ℚ :=
  prob_over_challenges (E := AcceptsAndBadTranscriptOnChallenges domain claim p adv)
