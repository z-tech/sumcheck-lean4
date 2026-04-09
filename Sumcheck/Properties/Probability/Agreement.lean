import CompPoly.Multivariate.CMvPolynomial

import Sumcheck.Properties.Probability.CountingAgreement
import Sumcheck.Properties.Probability.CountingPolynomials

@[simp] def prob_agreement_at_random_challenge
  {n} {𝔽} [CommRing 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (g h : CPoly.CMvPolynomial n 𝔽)
  (_h_not_equal : g ≠ h) : ℚ :=
    count_assignments_causing_agreement g h / count_all_assignments_n (𝔽 := 𝔽) n
