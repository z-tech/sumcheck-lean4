import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic


@[simp]
noncomputable def generate_prover_message (p : MvPolynomial (Fin 2) (ZMod 19)) : Fin 2 → ZMod 19 :=
  let sum_0 :=
      (List.range 2).foldl (fun acc x1 =>
        acc + MvPolynomial.eval ![0, x1] p)
      0
  let sum_1 :=
      (List.range 2).foldl (fun acc x1 =>
        acc + MvPolynomial.eval ![1, x1] p)
      0

  ![sum_0, sum_1]

namespace ProverTests

@[simp]
noncomputable def test_p : MvPolynomial (Fin 2) (ZMod 19) := 3 * MvPolynomial.X 0 * MvPolynomial.X 1 + 5 * MvPolynomial.X 0 + 1

  namespace BasicSanity

    @[simp]
    noncomputable def point_00 : (ZMod 19) := MvPolynomial.eval ![0, 0] test_p
    lemma point_00_val : point_00 = (1 : ZMod 19) := by
      simp [point_00, test_p]

    @[simp]
    noncomputable def point_01 : (ZMod 19) := MvPolynomial.eval ![1, 0] test_p
    lemma point_01_val : point_01 = (6 : ZMod 19) := by
      simp [point_00, test_p]
      ring_nf

    @[simp]
    noncomputable def point_10 : (ZMod 19) := MvPolynomial.eval ![0, 1] test_p
    lemma point_10_val : point_10 = (1 : ZMod 19) := by
      simp [point_10, test_p]

    @[simp]
    noncomputable def point_11 : (ZMod 19) := MvPolynomial.eval ![1, 1] test_p
    lemma point_11_val : point_11 = (9 : ZMod 19) := by
      simp [point_11, test_p]
      ring_nf

    @[simp]
    noncomputable def sum_0 : (ZMod 19) := point_00 + point_10
    lemma sum_0_val : sum_0 = (2 : ZMod 19) := by
      simp [point_11, test_p]
      ring_nf

    @[simp]
    noncomputable def sum_1 : (ZMod 19) := point_01 + point_11
    lemma sum_1_val : sum_1 = (15 : ZMod 19) := by
      simp [point_11, test_p]
      ring_nf

  end BasicSanity

  namespace generate_prover_message_Tests

    noncomputable def expected_sum_0 : (ZMod 19) := (2 : ZMod 19)
    lemma it_should_generate_sum_0_correctly : generate_prover_message test_p 0 = expected_sum_0 := by
      unfold generate_prover_message test_p expected_sum_0
      simp [List.foldl, List.flatMap, List.range, List.range.loop]
      ring_nf

    noncomputable def expected_sum_1 : (ZMod 19) := (15 : ZMod 19)
    lemma it_should_generate_sum_1_correctly : generate_prover_message test_p 1 = expected_sum_1 := by
      unfold generate_prover_message test_p expected_sum_1
      simp [List.foldl, List.flatMap, List.range, List.range.loop]
      ring_nf

  end generate_prover_message_Tests

end ProverTests
