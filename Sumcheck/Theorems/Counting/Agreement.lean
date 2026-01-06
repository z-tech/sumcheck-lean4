import Sumcheck.Theorems.Events.Agreement
import Sumcheck.Theorems.Universe.Polynomials

@[simp] def count_agreement_at_event
  {n} {𝔽} [CommRing 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (g h : CPoly.CMvPolynomial n 𝔽) : ℕ :=
  {assignment ∈ all_assignments_n n 𝔽 | AgreementAtEvent (g := g) (h := h) assignment}.card
