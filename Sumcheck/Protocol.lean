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
  -- verifier checks G_1(0) + G_1(1) =? G_0(2)
  -- transcript { prover_messages: [(2, 15), (11, 17)], verifier_messages: [2], is_accepted: true }

  -- setup
  @[simp]
  noncomputable def claim_0 : (ZMod 19) := (17 : ZMod 19)
  noncomputable def p_0 : MvPolynomial (Fin 2) (ZMod 19) := 3 * MvPolynomial.X 0 * MvPolynomial.X 1 + 5 * MvPolynomial.X 0 + 1

  -- round 0
  noncomputable def default_challenge : (ZMod 19) := 1
  noncomputable def prover_message_0 : Polynomial (ZMod 19) := generate_prover_message_from_sums (generate_sums_variablewise default_challenge p_0 0) (generate_sums_variablewise default_challenge p_0 1)
  noncomputable def verifier_check_0 : Bool := check_round claim_0 prover_message_0
  lemma verifier_check_0_is_correct : verifier_check_0 = true := by
    unfold verifier_check_0 prover_message_0
    simp [p_0, Fintype.piFinset, Finset.univ, Fintype.elems, List.finRange, List.ofFn, Fin.foldr, Fin.foldr.loop, Finset.pi, Multiset.map]
    decide
  noncomputable def verifier_challenge_0 : (ZMod 19) := (2 : ZMod 19)

  -- round 1
  noncomputable def claim_1 : (ZMod 19) := generate_claim verifier_challenge_0 prover_message_0
  noncomputable def prover_message_1 : Polynomial (ZMod 19) := generate_prover_message_from_sums (generate_sums_variablewise verifier_challenge_0 p_0 0) (generate_sums_variablewise verifier_challenge_0 p_0 1)
  noncomputable def expected_prover_message_1 : Polynomial (ZMod 19) := (Polynomial.X * 13) + Polynomial.C 2
  -- lemma prover_message_1_is_correct : prover_message_1 = expected_prover_message_1 := by
  --   unfold prover_message_1 expected_prover_message_1 verifier_challenge_0 generate_sums_variablewise p_0 generate_hypercube
  --   simp [p_0,  Finset.univ, Fintype.elems, List.finRange, List.ofFn, Fin.foldr, Fin.foldr.loop]
  --   congr

end __ProtocolTests__
