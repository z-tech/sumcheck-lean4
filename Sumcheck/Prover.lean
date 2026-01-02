import Mathlib.Data.ZMod.Basic

import Sumcheck.Polynomials

namespace __ProverTests__

  def test_p_mon_11 : CPoly.CMvMonomial 2 := ⟨#[1, 1], by decide⟩
  def test_p_mon_10   : CPoly.CMvMonomial 2 := ⟨#[1, 0], by decide⟩
  def test_p_mon_00    : CPoly.CMvMonomial 2 := ⟨#[0, 0], by decide⟩
  def test_p : CPoly.CMvPolynomial 2 (ZMod 19) :=
    CPoly.Lawful.fromUnlawful <|
      ((0 : CPoly.Unlawful 2 (ZMod 19)).insert test_p_mon_11 (3 : ZMod 19))
        |>.insert test_p_mon_10 (5 : ZMod 19)
        |>.insert test_p_mon_00  (1 : ZMod 19)

  namespace __generate_sums_variablewise_tests__

    def expected_sum_0 : (ZMod 19) := (2 : ZMod 19)
    lemma it_should_generate_sum_0_correctly : sum_over_boolean_extension ![] 0 test_p (by decide) = expected_sum_0 := by
      unfold sum_over_boolean_extension test_p expected_sum_0
      simp
      native_decide

    noncomputable def expected_sum_1 : (ZMod 19) := (15 : ZMod 19)
    lemma it_should_generate_sum_1_correctly : sum_over_boolean_extension ![] 1 test_p (by decide) = expected_sum_1 := by
      unfold sum_over_boolean_extension test_p expected_sum_1
      simp
      native_decide

  end __generate_sums_variablewise_tests__

  namespace __generate_prover_message_from_sums__

    instance : Fact (Nat.Prime 19) := ⟨by decide⟩
    def sum_0 : (ZMod 19) := (2 : ZMod 19)
    def sum_1 : (ZMod 19) := (15 : ZMod 19)
    def expected_prover_message_mon_1   : CPoly.CMvMonomial 1 := ⟨#[1], by decide⟩
    def expected_prover_message_mon_0   : CPoly.CMvMonomial 1 := ⟨#[0], by decide⟩
    def expected_prover_message : CPoly.CMvPolynomial 1 (ZMod 19) :=
      CPoly.Lawful.fromUnlawful <|
        ((0 : CPoly.Unlawful 1 (ZMod 19)).insert expected_prover_message_mon_1 (13 : ZMod 19))
          |>.insert expected_prover_message_mon_0 (2 : ZMod 19)

    lemma it_should_generate_prover_message_from_sums_correctly : lagrange_interpolation_n_points ![sum_0, sum_1] = expected_prover_message := by
      native_decide

  end __generate_prover_message_from_sums__

  namespace __BasicSanity__

    @[simp]
    def point_00 : (ZMod 19) := CPoly.CMvPolynomial.eval ![0, 0] test_p
    lemma point_00_val : point_00 = (1 : ZMod 19) := by
      native_decide

    @[simp]
    noncomputable def point_01 : (ZMod 19) := CPoly.CMvPolynomial.eval ![1, 0] test_p
    lemma point_01_val : point_01 = (6 : ZMod 19) := by
      simp
      native_decide

    @[simp]
    noncomputable def point_10 : (ZMod 19) := CPoly.CMvPolynomial.eval ![0, 1] test_p
    lemma point_10_val : point_10 = (1 : ZMod 19) := by
      simp
      native_decide

    @[simp]
    noncomputable def point_11 : (ZMod 19) := CPoly.CMvPolynomial.eval ![1, 1] test_p
    lemma point_11_val : point_11 = (9 : ZMod 19) := by
      simp
      native_decide

    @[simp]
    noncomputable def sum_0 : (ZMod 19) := point_00 + point_10
    lemma sum_0_val : sum_0 = (2 : ZMod 19) := by
      simp
      native_decide

    @[simp]
    noncomputable def sum_1 : (ZMod 19) := point_01 + point_11
    lemma sum_1_val : sum_1 = (15 : ZMod 19) := by
      simp
      native_decide

  end __BasicSanity__

end __ProverTests__
