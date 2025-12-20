import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

import Sumcheck.Utils

@[simp]
def verifier_check {𝔽} [CommRing 𝔽] [DecidableEq 𝔽]
  (expected_value_from_prev_round : 𝔽)
  (current_univariate_poly : MvPolynomial (Fin 1) 𝔽) : Bool :=
  decide (eval_at 0 current_univariate_poly + eval_at 1 current_univariate_poly = expected_value_from_prev_round)

@[simp]
noncomputable def verifier_generate_expected_value_next_round {𝔽} [CommRing 𝔽] [DecidableEq 𝔽]
  (current_univariate_poly : MvPolynomial (Fin 1) 𝔽)
  (current_challenge : 𝔽) : 𝔽 :=
  eval_at current_challenge current_univariate_poly

namespace __VerifierTests__

  noncomputable def test_prover_message : MvPolynomial (Fin 1) (ZMod 19) :=  MvPolynomial.C 13 *  MvPolynomial.X 0 +  MvPolynomial.C 2

  namespace __check_round_tests__

    lemma it_should_check_false_round_correctly : verifier_check (11 : ZMod 19) test_prover_message = false := by
      unfold verifier_check test_prover_message eval_at
      simp
      decide


    lemma it_should_check_true_round_correctly : verifier_check (17 : ZMod 19) test_prover_message = true := by
      unfold verifier_check test_prover_message eval_at
      simp
      decide

    def expected_check_round : Bool := false
    lemma it_should_check_false_round_correctly_general : ∀ (x : ZMod 19), x != 17 ->  verifier_check (x : ZMod 19) test_prover_message = false := by
      unfold verifier_check test_prover_message eval_at
      simp
      decide

  end __check_round_tests__

  namespace __generate_claim_tests__

    def expected_claim : (ZMod 19) := (9 : ZMod 19)
    lemma it_should_generate_claim_correctly : verifier_generate_expected_value_next_round test_prover_message (2 : ZMod 19) = expected_claim := by
      unfold verifier_generate_expected_value_next_round test_prover_message expected_claim eval_at
      simp
      decide

  end __generate_claim_tests__

end __VerifierTests__
