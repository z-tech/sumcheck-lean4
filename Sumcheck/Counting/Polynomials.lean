import Mathlib.Data.ZMod.Basic

import Sumcheck.Universe.Polynomials

@[simp]
def count_assignments
  {𝔽} (n : ℕ) [Fintype 𝔽] [DecidableEq 𝔽] : ℕ :=
  (all_assignments_n n 𝔽).card

-- TODO: move to Impl
@[simp]
def max_ind_degree
  {𝔽 : Type _} {n : ℕ} [CommSemiring 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽) : ℕ :=
  (Finset.univ : Finset (Fin n)).sup (fun i => CPoly.CMvPolynomial.degreeOf i p)

-- TODO: move to Impl
@[simp]
def ind_degree_k
  {𝔽 n} [CommSemiring 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽)
  (k : Fin n) : ℕ :=
  CPoly.CMvPolynomial.degreeOf k p
