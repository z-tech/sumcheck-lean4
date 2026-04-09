import Mathlib.Data.ZMod.Basic
import Sumcheck.Src.CMvPolynomial

abbrev field_size {𝔽} [Fintype 𝔽] : ℕ :=
  Fintype.card 𝔽

/-- The sumcheck soundness error bound: n * max_ind_degree(p) / |𝔽|. -/
noncomputable def soundness_error
  {𝔽 : Type _} {n : ℕ} [CommSemiring 𝔽] [Fintype 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽) : ℚ :=
  (n : ℚ) * (max_ind_degree p : ℚ) / (field_size (𝔽 := 𝔽) : ℚ)
