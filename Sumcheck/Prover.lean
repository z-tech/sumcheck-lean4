import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Bitwise

import CompPoly.CMvPolynomial
import CompPoly.CMvMonomial
import CompPoly.Lawful

import Sumcheck.Hypercube

open CPoly

def dropVar0Monomial {n : ℕ} (m : CPoly.CMvMonomial (n+1)) : CPoly.CMvMonomial n :=
  ⟨
    Array.ofFn (fun k : Fin n => m.toArray[k.1 + 1]!),
    by
      simp
  ⟩

def absorb_variable_zero
  {𝔽 : Type} [CommSemiring 𝔽] [BEq 𝔽] [LawfulBEq 𝔽] {n : ℕ}
  (a : 𝔽)
  (p : CPoly.CMvPolynomial (n+1) 𝔽) : CPoly.CMvPolynomial n 𝔽 :=
by
  -- fold over the underlying Unlawful term map of `p`
  let u' : CPoly.Unlawful n 𝔽 :=
    (p.1).foldl (init := (0 : CPoly.Unlawful n 𝔽))
      (fun acc m c =>
        let e0 : Nat := m.toArray[0]!
        let m' : CPoly.CMvMonomial n := dropVar0Monomial (n := n) m
        let c' : 𝔽 := c * a ^ e0
        -- add c' into acc at key m' (sum if present)
        acc.alter m' (fun
          | none      => some c'
          | some old  => some (old + c')))

  -- canonicalize (drops any zero coefficients) in a computable way
  exact CPoly.Lawful.fromUnlawful u'

@[simp]
def generate_sums_variablewise {𝔽} [CommRing 𝔽] [DecidableEq 𝔽]
  (challenges : Fin k → 𝔽) (hcard : k ≤ n) (p : CPoly.CMvPolynomial n 𝔽) : Fin 2 → 𝔽 :=
  match n with
  | 0 => ![0, 0]
  | Nat.succ m => -- NOTE: (Nat.succ m) = n
    let hypercube : Finset (Fin (Nat.succ m) → 𝔽) := generate_hypercube (Nat.succ m)
    let sum_0 : 𝔽 := hypercube.sum fun hypercube_point =>
      let point : Fin (Nat.succ m) → 𝔽 := generate_point_from_challenges challenges hypercube_point hcard
      if hypercube_point 0 == 0 then CPoly.CMvPolynomial.eval point p else 0
    let sum_1 : 𝔽 := hypercube.sum fun hypercube_point =>
      let point : Fin (Nat.succ m) → 𝔽 := generate_point_from_challenges challenges hypercube_point hcard
      if hypercube_point 0 == 1 then CPoly.CMvPolynomial.eval point p else 0
    ![sum_0, sum_1]

-- monomial for X₀ in 1 variable: exponent vector [1]
def mX0 : CPoly.CMvMonomial 1 :=
  ⟨#[1], by decide⟩

-- polynomial X₀ : CMvPolynomial 1 𝔽
def X0 {𝔽} [CommRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽] : CPoly.CMvPolynomial 1 𝔽 :=
  CPoly.Lawful.fromUnlawful
    ((0 : CPoly.Unlawful 1 𝔽).insert mX0 (1 : 𝔽))

/-- (sum₁ - sum₀) * X₀ + sum₀ as a CMvPolynomial. -/
def generate_prover_message_from_sums
  {𝔽} [CommRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (sum_0 sum_1 : 𝔽) : CPoly.CMvPolynomial 1 𝔽 :=
  (CPoly.Lawful.C (n := 1) (R := 𝔽) (sum_1 - sum_0)) * (X0 (𝔽 := 𝔽))
  + (CPoly.Lawful.C (n := 1) (R := 𝔽) sum_0)

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
    noncomputable def received_sum_0 : (ZMod 19) := generate_sums_variablewise ![] (by decide) test_p 0
    lemma it_should_generate_sum_0_correctly : received_sum_0 = expected_sum_0 := by
      unfold received_sum_0 generate_sums_variablewise test_p expected_sum_0
      simp
      native_decide

    noncomputable def expected_sum_1 : (ZMod 19) := (15 : ZMod 19)
    lemma it_should_generate_sum_1_correctly : generate_sums_variablewise ![] (by decide) test_p 1 = expected_sum_1 := by
      unfold generate_sums_variablewise test_p expected_sum_1
      simp
      native_decide

  end __generate_sums_variablewise_tests__

  namespace __generate_prover_message_from_sums__

    def sum_0 : (ZMod 19) := (2 : ZMod 19)
    def sum_1 : (ZMod 19) := (15 : ZMod 19)
    def expected_prover_message_mon_1   : CPoly.CMvMonomial 1 := ⟨#[1], by decide⟩
    def expected_prover_message_mon_0   : CPoly.CMvMonomial 1 := ⟨#[0], by decide⟩
    def expected_prover_message : CPoly.CMvPolynomial 1 (ZMod 19) :=
      CPoly.Lawful.fromUnlawful <|
        ((0 : CPoly.Unlawful 1 (ZMod 19)).insert expected_prover_message_mon_1 (13 : ZMod 19))
          |>.insert expected_prover_message_mon_0 (2 : ZMod 19)

    lemma it_should_generate_prover_message_from_sums_correctly : generate_prover_message_from_sums sum_0 sum_1 = expected_prover_message := by
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
