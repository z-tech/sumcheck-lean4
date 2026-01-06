import CompPoly.CMvPolynomial

import Sumcheck.Theorems.Counting.Agreement
import Sumcheck.Theorems.Counting.Polynomials

@[simp] def prob_agreement
  {n} {𝔽} [CommRing 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (g h : CPoly.CMvPolynomial n 𝔽)
  (_h_not_equal : g ≠ h) : ℚ := count_agreement_at_event g h / count_assignments (𝔽 := 𝔽) n
