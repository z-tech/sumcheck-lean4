import Mathlib.Data.ZMod.Basic

import Sumcheck.Impl.Polynomials

@[simp] def honest_prover_message
  {𝔽} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽)
  (challenges : Fin k → 𝔽)
  (hcard : k + 1 ≤ (n : ℕ)) : CPoly.CMvPolynomial 1 𝔽 :=
by
  classical
  let current_var_index : Fin n := ⟨k, hcard⟩
  let ind_degree_current_var := CPoly.CMvPolynomial.degreeOf current_var_index p
  let sums : Fin (ind_degree_current_var + 1) → 𝔽 := fun i =>
    sum_over_boolean_extension challenges i p hcard
  exact lagrange_interpolation_n_points sums
