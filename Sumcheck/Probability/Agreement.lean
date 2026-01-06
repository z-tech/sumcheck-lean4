import CompPoly.CMvPolynomial

import Sumcheck.Counting.Agreement
import Sumcheck.Counting.Polynomials

@[simp] def prob_agreement_at_random_challenge
  {n} {𝔽} [CommRing 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (g h : CPoly.CMvPolynomial n 𝔽)
  (_h_not_equal : g ≠ h) : ℚ := count_agreement_at_event g h / count_assignments (𝔽 := 𝔽) n
