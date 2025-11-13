import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.ZMod.Basic

import Sumcheck.Prover
import Sumcheck.Verifier

namespace __ProtocolTests__

  -- p = 3 * x_0 * x_1 + 5 * x_0 + 1, true sum = 17 mod 19
  -- round 0 prover sums over all points
  -- point: [0, 0] -> 1
  -- point: [1, 0] -> 6
  -- point: [0, 1] -> 1
  -- point: [1, 1] -> 9
  -- prover interpolates ((0, 2), (1, 15)) and sends univariate G_0 = 13 * x + 2
  -- verifier checks G_0(0) + G_0(1) =? 17 mod 19
  -- verifier samples a challenge: 2
  -- round 1 prover sums over smaller points after absorbing verifier challenge
  -- point: [2, 0] -> 11
  -- point: [2, 1] -> 17
  -- prover interpolates ((0, 11), (1, 17)) and sends univariate G_1 = 6 * x + 11
  -- verifier checks G_0(0) + G_0(1) =? G_0(2)
  -- transcript { prover_messages: [(2, 15), (11, 17)], verifier_messages: [2], is_accepted: true }

  -- setup
  @[simp]
  noncomputable def initial_claim : (ZMod 19) := (17 : ZMod 19)
  noncomputable def p : MvPolynomial (Fin 2) (ZMod 19) := 3 * MvPolynomial.X 0 * MvPolynomial.X 1 + 5 * MvPolynomial.X 0 + 1

  -- round 0
  noncomputable def prover_message_0 : Polynomial (ZMod 19) := generate_prover_message_from_sums (generate_sums_variablewise p 0) (generate_sums_variablewise p 1)
  noncomputable def verifier_check_0 : Bool := check_round initial_claim prover_message_0
  -- TODO (z-tech): this depends on hypercube
  -- lemma verifier_check_0_is_true : verifier_check_0 = true := by
  --   unfold verifier_check_0 check_round initial_claim prover_message_0 generate_sums_variablewise generate_hypercube generate_prover_message_from_sums nat_to_point Polynomial.eval MvPolynomial.eval
  --   simp [Finset.image, Finset.range, Nat.testBit]

end __ProtocolTests__
