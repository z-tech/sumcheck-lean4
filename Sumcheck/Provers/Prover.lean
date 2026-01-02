import CompPoly.CMvPolynomial
import Mathlib.Data.ZMod.Basic

import Sumcheck.Prover
import Sumcheck.Polynomials

class Prover (𝔽 : Type _) [CommRing 𝔽] where
  num_rounds : ℕ
  current_round : ℕ
  hround_num : current_round < num_rounds
  claim_polynomial : CPoly.CMvPolynomial num_rounds 𝔽
  claim_polynomial_max_ind_degree: ℕ
  challenges : Fin current_round → 𝔽
  next_message : (hround_num : current_round < num_rounds) → (challenge : 𝔽) → CPoly.CMvPolynomial 1 𝔽 × Prover 𝔽

def ClassicProver (𝔽 : Type _) [Field 𝔽] [DecidableEq 𝔽]
  (num_rounds : ℕ)
  (current_round : ℕ)
  (hround_num : current_round < num_rounds)
  (claim_polynomial : CPoly.CMvPolynomial num_rounds 𝔽)
  (claim_polynomial_max_ind_degree: ℕ)
  (challenges : Fin current_round → 𝔽) :
  Prover 𝔽 :=
by
  let this_num_rounds := num_rounds
  let this_current_round := current_round
  let this_hround_num := hround_num
  let this_claim_polynomial := claim_polynomial
  let this_claim_polynomial_max_ind_degree := claim_polynomial_max_ind_degree
  let this_challenges := challenges
  exact
  {
    num_rounds := this_num_rounds
    current_round := this_current_round
    hround_num := this_hround_num
    claim_polynomial := this_claim_polynomial
    claim_polynomial_max_ind_degree := this_claim_polynomial_max_ind_degree
    challenges := this_challenges
    next_message := fun _challenge =>
      -- for i in 0..max_ind_degree
    let sums : Fin claim_polynomial_max_ind_degree → 𝔽 := fun i =>
      sum_over_boolean_extension this_challenges ((i : ℕ) : 𝔽) this_claim_polynomial hround_num
    let message := lagrange_interpolation_n_points sums
    message
  }
