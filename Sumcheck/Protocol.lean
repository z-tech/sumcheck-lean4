import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.ZMod.Basic

import Sumcheck.Prover
import Sumcheck.Verifier
import Sumcheck.Round
import Sumcheck.Utils

namespace __ProtocolTests__
  namespace __TwoVariableSumcheck__
    -- p = 3 * x_0 * x_1 + 5 * x_0 + 1, true sum = 17 mod 19
    -- round 0 prover sums over all points
    -- point: [0, 0] -> 1
    -- point: [1, 0] -> 6
    -- point: [0, 1] -> 1
    -- point: [1, 1] -> 9
    -- prover interpolates ((0, 2), (1, 15)) and sends univariate G_0 = 13 * x + 2
    -- verifier checks G_0(0) + G_0(1) =? 17 mod 19
    -- verifier samples a challenge: 2
    -- verifier computes next round claim: 9
    -- round 1 prover sums over smaller points after absorbing verifier challenge
    -- point: [2, 0] -> 11
    -- point: [2, 1] -> 17
    -- prover interpolates ((0, 11), (1, 17)) and sends univariate G_1 = 6 * x + 11
    -- verifier checks G_1(0) + G_1(1) =? G_0(2)
    -- verifier samples a challenge: 3
    -- verifier computes next round claim: 10 <-- this is never used
    -- transcript { prover_messages: [(2, 15), (11, 17)], verifier_messages: [2] }

    -- setup
    def claim_0 : (ZMod 19) := (17 : ZMod 19)
    def p_0_mon_11 : CPoly.CMvMonomial 2 := ⟨#[1, 1], by decide⟩
    def p_0_mon_10   : CPoly.CMvMonomial 2 := ⟨#[1, 0], by decide⟩
    def p_0_mon_00    : CPoly.CMvMonomial 2 := ⟨#[0, 0], by decide⟩
    def p_0 : CPoly.CMvPolynomial 2 (ZMod 19) :=
      CPoly.Lawful.fromUnlawful <|
        ((0 : CPoly.Unlawful 2 (ZMod 19)).insert p_0_mon_11 (3 : ZMod 19))
          |>.insert p_0_mon_10 (5 : ZMod 19)
          |>.insert p_0_mon_00  (1 : ZMod 19)

    -- round 0
    def simulated_challenge_0 : (ZMod 19) := 2
    def prover_output_0 := prover_move 2 p_0 simulated_challenge_0 -- message = 13x + 2
    def round_poly_0 := prover_output_0.1
    def verifier_output_0 := verifier_move claim_0 round_poly_0 simulated_challenge_0
    lemma verifier_check_0_is_correct : verifier_output_0 = (9 : ZMod 19) := by
      unfold verifier_output_0 round_poly_0 prover_output_0 verifier_move verifier_check prover_move
        simulated_challenge_0 p_0
      simp
      native_decide

    -- round 1
    @[simp]
    def claim_1 := verifier_output_0.getD 0
    def p_1 := prover_output_0.2

    def prover_output_1 := prover_move 1 p_1 simulated_challenge_0 -- message = 6x + 11
    def round_poly_1 := prover_output_1.1
    def simulated_challenge_1 : (ZMod 19) := 3
    def verifier_output_1 := verifier_move claim_1 round_poly_1 simulated_challenge_1
    lemma verifier_check_1_is_correct : verifier_output_1 = (10 : ZMod 19) := by
      unfold verifier_output_1 round_poly_1 prover_output_1 verifier_move verifier_check prover_move
        simulated_challenge_0 simulated_challenge_1 p_1
      simp
      native_decide
  end __TwoVariableSumcheck__
end __ProtocolTests__
