import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

@[simp]
noncomputable def check_round {𝔽} [CommRing 𝔽] [DecidableEq 𝔽] (claim : 𝔽) (prover_message : Polynomial 𝔽) : Bool :=
  decide (Polynomial.eval 0 prover_message + Polynomial.eval 1 prover_message = claim)


namespace __VerifierTests__

  namespace __check_round_tests__

    noncomputable def test_g : Polynomial (ZMod 19) :=  Polynomial.C 13 *  Polynomial.X +  Polynomial.C 2

    def expected_check_round_false : Bool := false
    lemma it_should_check_false_round_correctly : check_round (11 : ZMod 19) test_g = expected_check_round_false := by
      unfold check_round test_g expected_check_round_false
      simp
      ring_nf
      decide

    def expected_check_round_true : Bool := true
    lemma it_should_check_true_round_correctly : check_round (17 : ZMod 19) test_g = expected_check_round_true := by
      unfold check_round test_g expected_check_round_true
      simp
      ring_nf

  end __check_round_tests__

end __VerifierTests__
