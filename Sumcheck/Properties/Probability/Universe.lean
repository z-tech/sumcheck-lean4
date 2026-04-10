import InteractiveProtocol.Properties.Probability
import CompPoly.Multivariate.CMvPolynomial

-- all_assignments_n is just allChallenges with swapped argument order
-- kept as alias for backwards compatibility during migration
abbrev all_assignments_n (n : ℕ) (𝔽 : Type _) [Fintype 𝔽] : Finset (Fin n → 𝔽) :=
  allChallenges 𝔽 n
