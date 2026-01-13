import Sumcheck.Events.Agreement
import Sumcheck.Universe.Polynomials

@[simp] def count_assignments_causing_agreement
  {n} {𝔽} [CommRing 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (g h : CPoly.CMvPolynomial n 𝔽) : ℕ :=
  {assignment ∈ all_assignments_n n 𝔽 | AgreementAtEvent g h assignment}.card
