import CompPoly.CMvPolynomial
import Mathlib.Data.ZMod.Basic

import Sumcheck.Prover

class Prover (𝔽 : Type _) [CommRing 𝔽] where
  num_rounds : ℕ
  current_round : ℕ
  hround_num : current_round < num_rounds
  claim_polynomial : CPoly.CMvPolynomial num_rounds 𝔽
  claim_polynomial_max_ind_degree: ℕ
  challenges : Fin current_round → 𝔽
  next_message : (hround_num : current_round < num_rounds) → (challenge : 𝔽) → CPoly.CMvPolynomial 1 𝔽 × Prover 𝔽

def ClassicProver (𝔽 : Type _) [CommRing 𝔽] [DecidableEq 𝔽]
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
      -- TODO: this should be loop like for i in 0..max_ind_degree
      have hle : current_round ≤ num_rounds := Nat.le_of_lt this_hround_num
      let sum0 := sum_over_boolean_extension this_challenges 0 this_claim_polynomial hle
      let sum1 := sum_over_boolean_extension this_challenges 1 this_claim_polynomial hle
      -- TODO: then use all of those points in 0..max_ind_degree to make unique univariate poly
      let message := generate_prover_message_from_sums sum0 sum1
      message
  }
