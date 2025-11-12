import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

  -- simp [test_p, List.range, List.foldl, List.flatMap, List.map, List.range.loop, coeff]
  -- ring_nf
  -- rfl

-- NOTE 1: Sumcheck over univariate P (kind of) exists, but is useless (it provides neither soundness nor faster verification)
-- NOTE 2: Do not confuse multivariate polynomial P with univariate polynomial G_i used in each round for algebraic checks

-- EXAMPLE A showing why sumcheck over univariate P is not useful
-- P = 3 * x + 1, true sum = 5 mod 19
-- round 0 prover sums over all points
-- point: [0] -> 1
-- point: [1] -> 4
-- prover interpolates ((0, 1), (1, 4)) and sends g0 = 3 * x + 1 <-- turns out the computed G_0 == P, so this accomplished nothing
-- verifier checks G_0(0) + G_0(1) =? 5
-- protocol transcript { prover_messages: [(1, 4)], verifier_messages: [], is_accepted: true }


-- EXAMPLE B showing why sumcheck over multivariate P is useful
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

-- structure Round (𝔽 : Type)  [Semiring 𝔽] where
--   -- inputs
--   g_i: Polynomial 𝔽
--   claim : 𝔽
--   -- outputs
--   is_accepted : Bool
--   new_challenge: 𝔽 -- randomly sampled 𝔽
--   new_claim: F -- Polynomial.eval new_challenge g_i

-- -- setup
-- @[simp] lemma decide_zero_eq_one_mod19 :
--   ((0 : ZMod 19) = 1) = false := by decide
-- @[simp] lemma decide_one_eq_one_mod19 :
--   ((1 : ZMod 19) = 0) = false := by decide

-- @[simp]
-- noncomputable def g_i (p : MvPolynomial (Fin 2) (ZMod 19)) : Polynomial (ZMod 19) :=
--   let sum_0 :=
--       (List.range 2).foldl (fun acc x1 =>
--         acc + MvPolynomial.eval ![0, x1] p)
--       0
--   let sum_1 :=
--       (List.range 2).foldl (fun acc x1 =>
--         acc + MvPolynomial.eval ![1, x1] p)
--       0
--   Polynomial.C sum_0 + Polynomial.C (sum_1 - sum_0) * Polynomial.X


-- @[simp]
-- noncomputable def test_claim : (ZMod 19) := (17 : ZMod 19)
-- example : computed_g_0 = expected_g_0 := by
--   unfold computed_g_0 expected_g_0
--   simp [g_i, test_p, List.range, List.foldl, List.flatMap, List.map, List.range.loop]
--   ring_nf

-- simulate round 0 input
-- set_option pp.notation false
-- set_option pp.all true
-- @[simp]
-- noncomputable def g_0' : Polynomial (ZMod 19) := 13 *  X + 2
-- example : g_0 = 0 := by
--   simp [List.range, List.range.loop]
--   norm_num
--   ring_nf

-- -- 13 * X + 2 -- prover just summed over the hypercube p(...) and interpolated a univariate g

-- @[simp]
-- noncomputable def oracle_0 (x : ZMod 19) : ZMod 19 := eval x g_0

-- -- @[simp]
-- -- noncomputable def claim_0 : (ZMod 19) := (17 : ZMod 19) -- equal to global
-- -- test_claim in round 0

-- -- simulate round 1 output

-- -- TODO verifier check is oracle_0(0) + oracle_0(1) =? claim_0 passes

-- -- @[simp]
-- -- noncomputable def challenge_0 : (ZMod 19) := (2 : ZMod 19) -- randomly sampled by verifier
-- variable (challenge_0 : ZMod 19)


-- @[simp]
-- noncomputable def claim_1 : (ZMod 19) := oracle_0 challenge_0


-- -- round 1 input
-- @[simp]
-- noncomputable def g_1 : Polynomial (ZMod 19) :=
--   let sum_0 :=
--       (List.range 2).foldl (fun acc2 x1 =>
--         if decide (x1 = 1) then acc2 else acc2 + test_oracle' challenge_0 x1)
--       0
--   let sum_1 :=
--       (List.range 2).foldl (fun acc2 x1 =>
--         if decide (x1 = 1) then acc2 + test_oracle' challenge_0 x1 else acc2)
--       0
--   (C sum_0 + (C (sum_1-sum_0)) * X)

-- -- @[simp]
-- -- noncomputable def g_1 : Polynomial (ZMod 19) := 6 * X + 11 -- prover just summed over the hypercube p(challenge_0, ..) and interpolated a univariate g

-- @[simp]
-- noncomputable def oracle_1 (x : ZMod 19): (ZMod 19) := eval x (g_1 challenge_0)

-- -- claim_1 is also input
-- @[simp]
-- def verifier_move {𝔽} [Semiring 𝔽] : List 𝔽  := [0, 1]

-- @[simp]
-- noncomputable def verifier {𝔽} [DecidableEq 𝔽] [Semiring 𝔽] (verifier_move : List 𝔽) (claim : 𝔽) (oracle : 𝔽 → 𝔽) :=
--       decide ((verifier_move.map oracle).sum = claim)

-- -- round 1 output
-- example : verifier verifier_move (claim_1 challenge_0) (oracle_1 challenge_0) = true := by
--    simp [List.range, List.range.loop]
--    ring
-- TODO verifier check is oracle_1(0) + oracle_1(1) =? claim_1 passes

-- there are no more variables so the protocol ends





-- -- we want to test the second round of EXAMPLE B below

-- noncomputable def test_sumcheck_round_as_IOR {𝔽} [DecidableEq 𝔽] [Semiring 𝔽] (prover : 𝔽 -> (𝔽 → 𝔽) -> Claim 𝔽) (oracle : 𝔽 → 𝔽)  (challenge : 𝔽) : IOR 𝔽  :=
--   let claim := prover challenge oracle
--   let check := verifier verifier_move claim oracle challenge
--   { oracle := oracle,
--     verifier_move := verifier_move,
--     claim := claim,
--     challenge := challenge,
--     verifier_check := check }

-- theorem soundness_IO {𝔽} [DecidableEq 𝔽] [Semiring 𝔽] : ∀ (prover : 𝔽 -> (𝔽 → 𝔽) -> Claim 𝔽) (challenge: 𝔽) (oracle : 𝔽 → 𝔽),
--     let claim_from_prover := prover challenge oracle;
--     let do_one_round := test_sumcheck_round_as_IOR prover oracle challenge;
--     (match claim_from_prover with
--     | Claim.scalar c => c = (verifier_move.map oracle).sum
--     | Claim.poly inner_round_polynomial =>
--      (Polynomial.eval challenge inner_round_polynomial) = (verifier_move.map oracle).sum) ->
--     Pr ( do_one_round.verifier_check = True) <= deg(f)/ |F|  := by sorry


  --  Pr[verifier_check == true] <= deg(f)/ |F|


-- noncomputable def test_sumcheck_round_as_IOR' : IOR (ZMod 19) :=
--   test_sumcheck_round_as_IOR (fun _challenge _oracle => test_claim)  test_oracle test_challenge


-- #simp test_sumcheck_round_as_IOR'.verifier_check

-- if claim == SUM x in {0,1} f(x), Pr[verifier_check == true] == 1
-- else .. claim != SUM x in {0,1} f(x), Pr[verifier_check == true] <= deg(f)/ |F|

-- @[simp]
-- noncomputable def test_p : MvPolynomial (Fin 2) (ZMod 19) := 3 * MvPolynomial.X 0 * MvPolynomial.X 1 + 5 * MvPolynomial.X 0 + 1

-- @[simp]
-- noncomputable def point_00 : (ZMod 19) := MvPolynomial.eval ![0, 0] test_p
-- lemma point_00_val : point_00 = (1 : ZMod 19) := by
--   simp [point_00, test_p]

-- @[simp]
-- noncomputable def point_01 : (ZMod 19) := MvPolynomial.eval ![1, 0] test_p
-- lemma point_01_val : point_01 = (6 : ZMod 19) := by
--   simp [point_00, test_p]
--   ring_nf

-- @[simp]
-- noncomputable def point_10 : (ZMod 19) := MvPolynomial.eval ![0, 1] test_p
-- lemma point_10_val : point_10 = (1 : ZMod 19) := by
--   simp [point_10, test_p]

-- @[simp]
-- noncomputable def point_11 : (ZMod 19) := MvPolynomial.eval ![1, 1] test_p
-- lemma point_11_val : point_11 = (9 : ZMod 19) := by
--   simp [point_11, test_p]
--   ring_nf

-- @[simp]
-- noncomputable def sum_0 : (ZMod 19) := point_00 + point_10
-- lemma sum_0_val : sum_0 = (2 : ZMod 19) := by
--   simp [point_11, test_p]
--   ring_nf

-- @[simp]
-- noncomputable def sum_1 : (ZMod 19) := point_01 + point_11
-- lemma sum_1_val : sum_1 = (15 : ZMod 19) := by
--   simp [point_11, test_p]
--   ring_nf


-- @[simp]
-- noncomputable def coeff : (ZMod 19) := sum_1 - sum_0
-- lemma coeff_val : coeff = (13 : ZMod 19) := by
--   simp [coeff, test_p]
--   ring_nf

-- @[simp]
-- noncomputable def test_p : MvPolynomial (Fin 2) (ZMod 19) := 3 * MvPolynomial.X 0 * MvPolynomial.X 1 + 5 * MvPolynomial.X 0 + 1

-- @[simp]
-- noncomputable def g_i (p : MvPolynomial (Fin 2) (ZMod 19)) : Fin 2 → ZMod 19 :=
--   let sum_0 :=
--       (List.range 2).foldl (fun acc x1 =>
--         acc + MvPolynomial.eval ![0, x1] p)
--       0
--   let sum_1 :=
--       (List.range 2).foldl (fun acc x1 =>
--         acc + MvPolynomial.eval ![1, x1] p)
--       0

--   ![sum_0, sum_1]

-- lemma sum_0_val : g_i test_p 0 = (2 : ZMod 19) := by
--   unfold g_i test_p
--   simp [List.foldl, List.flatMap, List.range, List.range.loop]
--   ring_nf

-- lemma sum_1_val : g_i test_p 1 = (15 : ZMod 19) := by
--   unfold g_i test_p
--   simp [List.foldl, List.flatMap, List.range, List.range.loop]
--   ring_nf






-- noncomputable def expected_g_0 : Polynomial (ZMod 19) :=  Polynomial.C 13 *  Polynomial.X +  Polynomial.C 2
-- noncomputable def computed_g_0 : Polynomial (ZMod 19) := g_i test_p

-- lemma equal_value : expected_g_0 = computed_g_0 := by
--   unfold computed_g_0 expected_g_0
--   simp [List.flatMap, List.range, List.range.loop]
--   ring_nf
--   congr
--   -- aesop
