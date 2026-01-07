import CompPoly.CMvPolynomial

import Sumcheck.Events.Accepts
import Sumcheck.Probability.Challenges

noncomputable def soundness_prob
  {𝔽 n} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (claim : 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (adv : Adversary 𝔽 n) : ℚ :=
  prob_over_challenges (E := AcceptsAndBadOnChallenges claim p adv)
