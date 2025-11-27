import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

import Sumcheck.Utils

@[simp]
def check_round
  {𝔽} [CommRing 𝔽] [DecidableEq 𝔽]
  (claim : 𝔽) (prover_message : MvPolynomial (Fin 1) 𝔽) : Bool :=
  decide (eval_at 0 prover_message + eval_at 1 prover_message = claim)

@[simp]
noncomputable def generate_claim {𝔽} [CommRing 𝔽] [DecidableEq 𝔽] (challenge : 𝔽) (prover_message : MvPolynomial (Fin 1) 𝔽) : 𝔽 :=
  eval_at challenge prover_message

namespace __VerifierTests__

  noncomputable def test_prover_message : MvPolynomial (Fin 1) (ZMod 19) :=  MvPolynomial.C 13 *  MvPolynomial.X 0 +  MvPolynomial.C 2

  namespace __check_round_tests__

    lemma it_should_check_false_round_correctly : check_round (11 : ZMod 19) test_prover_message = false := by
      unfold check_round test_prover_message eval_at
      simp
      decide


    lemma it_should_check_true_round_correctly : check_round (17 : ZMod 19) test_prover_message = true := by
      unfold check_round test_prover_message eval_at
      simp
      decide

    def expected_check_round : Bool := false
    lemma it_should_check_false_round_correctly_general : ∀ (x : ZMod 19), x != 17 ->  check_round (x : ZMod 19) test_prover_message = false := by
      unfold check_round test_prover_message eval_at
      simp
      decide

  end __check_round_tests__

  namespace __generate_claim_tests__

    def expected_claim : (ZMod 19) := (9 : ZMod 19)
    lemma it_should_generate_claim_correctly : generate_claim (2 : ZMod 19) test_prover_message = expected_claim := by
      unfold generate_claim test_prover_message expected_claim eval_at
      simp
      decide

  end __generate_claim_tests__

end __VerifierTests__
