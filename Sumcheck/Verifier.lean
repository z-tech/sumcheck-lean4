import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

@[simp]
noncomputable def check_round {𝔽} [CommRing 𝔽] [DecidableEq 𝔽] (claim : 𝔽) (prover_message : Polynomial 𝔽) : Bool :=
  decide (Polynomial.eval 0 prover_message + Polynomial.eval 1 prover_message = claim)

@[simp]
noncomputable def generate_claim {𝔽} [CommRing 𝔽] [DecidableEq 𝔽] (challenge : 𝔽) (prover_message : Polynomial 𝔽) : 𝔽 :=
  Polynomial.eval challenge prover_message

namespace __VerifierTests__

  noncomputable def test_prover_message : Polynomial (ZMod 19) :=  Polynomial.C 13 *  Polynomial.X +  Polynomial.C 2

  namespace __check_round_tests__

    def expected_check_round_false : Bool := false
    lemma it_should_check_false_round_correctly : check_round (11 : ZMod 19) test_prover_message = expected_check_round_false := by
      unfold check_round test_prover_message expected_check_round_false
      simp
      ring_nf
      decide

    def expected_check_round_true : Bool := true
    lemma it_should_check_true_round_correctly : check_round (17 : ZMod 19) test_prover_message = expected_check_round_true := by
      unfold check_round test_prover_message expected_check_round_true
      simp
      ring_nf

    def expected_check_round : Bool := false
    lemma it_should_check_false_round_correctly_general : ∀ (x : ZMod 19), x != 17 ->  check_round (x : ZMod 19) test_prover_message = expected_check_round_false := by
      unfold check_round test_prover_message expected_check_round_false
      simp
      ring_nf
      decide

  end __check_round_tests__

  namespace __generate_claim_tests__

    def expected_claim : (ZMod 19) := (9 : ZMod 19)
    lemma it_should_generate_claim_correctly : generate_claim (2 : ZMod 19) test_prover_message = expected_claim := by
      unfold generate_claim test_prover_message expected_claim
      simp
      decide

  end __generate_claim_tests__

end __VerifierTests__
