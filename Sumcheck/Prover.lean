import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Bitwise

import Sumcheck.Hypercube

@[simp]
noncomputable def generate_sums_variablewise {𝔽} [CommSemiring 𝔽] [DecidableEq 𝔽] (p : MvPolynomial (Fin n) 𝔽) : Fin 2 → 𝔽 :=
  match n with
  | Nat.zero => ![0, 0]
  | Nat.succ m =>
    let hypercube : Finset (Fin m.succ → 𝔽) := generate_hypercube m.succ
    let sum_0 : 𝔽 := hypercube.sum (fun x => if x 0 = 0 then MvPolynomial.eval x p else 0)
    let sum_1 : 𝔽 := hypercube.sum (fun x => if x 0 = 1 then MvPolynomial.eval x p else 0)
    ![sum_0, sum_1]

@[simp]
noncomputable def generate_prover_message_from_sums {𝔽} [CommRing 𝔽] (sum_0 : 𝔽) (sum_1 : 𝔽) : Polynomial 𝔽 :=
  Polynomial.C (sum_1 - sum_0) *  Polynomial.X +  Polynomial.C sum_0

namespace __ProverTests__

  @[simp]
  noncomputable def test_p : MvPolynomial (Fin 2) (ZMod 19) := 3 * MvPolynomial.X 0 * MvPolynomial.X 1 + 5 * MvPolynomial.X 0 + 1

  namespace __generate_sums_variablewise_tests__

    -- TODO (z-tech): if I can solve "it_should_generate_hypercube_1_correctly" in a generic way, then these should be solvable
    noncomputable def expected_sum_0 : (ZMod 19) := (2 : ZMod 19)
    -- lemma it_should_generate_sum_0_correctly : generate_sums_variablewise test_p 0 = expected_sum_0 := by
    --   unfold generate_sums_variablewise test_p expected_sum_0
    --   simp [List.foldl, List.flatMap, List.range, List.range.loop]
    --   ring_nf

    noncomputable def expected_sum_1 : (ZMod 19) := (15 : ZMod 19)
    -- lemma it_should_generate_sum_1_correctly : generate_sums_variablewise test_p 1 = expected_sum_1 := by
    --   unfold generate_sums_variablewise test_p expected_sum_1
    --   simp [List.foldl, List.flatMap, List.range, List.range.loop, Finset.range, Finset.image, nat_to_point]
    --   ring_nf

  end __generate_sums_variablewise_tests__

  namespace __generate_prover_message_from_sums__

    def sum_0 : (ZMod 19) := (2 : ZMod 19)
    def sum_1 : (ZMod 19) := (15 : ZMod 19)
    noncomputable def expected_prover_message : Polynomial (ZMod 19) :=  Polynomial.C 13 *  Polynomial.X +  Polynomial.C 2
    lemma it_should_generate_prover_message_from_sums_correctly : generate_prover_message_from_sums sum_0 sum_1 = expected_prover_message := by
      unfold generate_prover_message_from_sums expected_prover_message
      congr

  end __generate_prover_message_from_sums__

  namespace __BasicSanity__

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

  end __BasicSanity__

end __ProverTests__
