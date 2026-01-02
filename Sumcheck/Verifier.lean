import CompPoly.CMvPolynomial
import CompPoly.CMvMonomial
import CompPoly.Lawful
import Mathlib.Data.ZMod.Basic

@[simp]
def verifier_check {𝔽} [CommRing 𝔽] [DecidableEq 𝔽]
  (expected_value_from_prev_round : 𝔽)
  (current_univariate_poly : CPoly.CMvPolynomial 1 𝔽) : Bool :=
  decide (
    CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ => 0) current_univariate_poly +
    CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ => 1) current_univariate_poly =
    expected_value_from_prev_round
  )

@[simp]
def verifier_generate_expected_value_next_round {𝔽} [CommRing 𝔽] [DecidableEq 𝔽]
  (current_univariate_poly : CPoly.CMvPolynomial 1 𝔽)
  (current_challenge : 𝔽) : 𝔽 :=
  CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ => current_challenge) current_univariate_poly

namespace __VerifierTests__

  @[simp]
  def mX : CPoly.CMvMonomial 1 := ⟨#[1], by decide⟩
  @[simp]
  def X0 : CPoly.CMvPolynomial 1 (ZMod 19) :=
    CPoly.Lawful.fromUnlawful
      ((0 : CPoly.Unlawful 1 (ZMod 19)).insert mX (1 : ZMod 19))
  @[simp]
  def test_prover_message : CPoly.CMvPolynomial 1 (ZMod 19) :=
    (CPoly.Lawful.C (n := 1) (R := ZMod 19) (13 : ZMod 19)) * X0
    + (CPoly.Lawful.C (n := 1) (R := ZMod 19) (2 : ZMod 19))

  namespace __check_round_tests__

    lemma it_should_check_false_round_correctly : verifier_check (11 : ZMod 19) test_prover_message = false := by
      unfold verifier_check test_prover_message
      simp
      native_decide


    lemma it_should_check_true_round_correctly : verifier_check (17 : ZMod 19) test_prover_message = true := by
      unfold verifier_check test_prover_message
      simp
      native_decide

  end __check_round_tests__

  namespace __generate_claim_tests__

    def expected_claim : (ZMod 19) := (9 : ZMod 19)
    lemma it_should_generate_claim_correctly : verifier_generate_expected_value_next_round test_prover_message (2 : ZMod 19) = expected_claim := by
      unfold verifier_generate_expected_value_next_round test_prover_message expected_claim
      simp
      native_decide

  end __generate_claim_tests__

end __VerifierTests__
