import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Data.ZMod.Basic

-- REALIZATION: Sumcheck over univariate p ~kind of~ exists, but is useless (it provides zero soundness nor faster verification)
-- REMINDER: Do not confuse Polynomial P (multivariate, what we're summing over) and Polynomial g_i (univariate round polynomials used for algebraic checks)
-- SEE EXAMPLES: A & B at bottom of file
-- PROPOSAL: focus on inner rounds (> round 0) and handle round 0 later in the IOP?


open Polynomial MvPolynomial

structure IOR (𝔽 : Type)  [Semiring 𝔽] where
  -- inputs
  oracle: 𝔽 → 𝔽 -- the univariate polynomial g_i given by the prover (verifier queries at verifier_move = {0, 1})
  verifier_move : List 𝔽
  claim : 𝔽 -- this is a scalar value computed by the verifier for round i as claim_i = g_i-1(challenge_i-1)
  -- outputs
  verifier_check : Bool -- Did this round pass? verifier checks SUM i in verifier_moves oracle(i) =? claim
  new_challenge: 𝔽 -- randomly sampled new challenge_i <-- the prover needs this to do their next thing
  new_claim: F -- the claim for the next round oracle(new_challenge) <-- the verifier needs this to do their next thing

-- setup
@[simp]
noncomputable def test_polynomial : MvPolynomial (Fin 2) (ZMod 19) := 3 * X 0 * X 1 + 5 * X 0 + 1

@[simp]
noncomputable def test_oracle : (ZMod 19) × (ZMod 19) → ZMod 19 :=
  fun (x₀, x₁) => eval (fun i => if i = 0 then x₀ else x₁) test_polynomial

@[simp]
noncomputable def test_claim : (ZMod 19) := (17 : ZMod 19)

-- simulate round 0 input
@[simp]
noncomputable def g_0 : Polynomial (ZMod 19) :=13 * X + 2 -- prover just summed over the hypercube p(...) and interpolated a univariate g

@[simp]
noncomputable def oracle_0 : Polynomial (ZMod 19) := evaluate g_0 at x

@[simp]
noncomputable def claim_0 : (ZMod 19) := (17 : ZMod 19) -- equal to global test_claim in round 0

-- simulate round 1 output

-- TODO verifier check is oracle_0(0) + oracle_0(1) =? claim_0 passes

@[simp]
noncomputable def challenge_0 : (ZMod 19) := (2 : ZMod 19) -- randomly sampled by verifier

@[simp]
noncomputable def claim_1 : (ZMod 19) := oracle_0(challenge_0)

-- round 1 input

@[simp]
noncomputable def g_1 : Polynomial (ZMod 19) := 6 * X + 11 -- prover just summed over the hypercube p(challenge_0, ..) and interpolated a univariate g

@[simp]
noncomputable def oracle_1 : Polynomial (ZMod 19) := evaluate g_1 at x

-- claim_1 is also input

-- round 1 output

-- TODO verifier check is oracle_1(0) + oracle_1(1) =? claim_1 passes

-- there are no more variables so the protocol ends




noncomputable def verifier {𝔽} [DecidableEq 𝔽] [Semiring 𝔽] (verifier_move : List 𝔽) (claim : 𝔽) (oracle : 𝔽 → 𝔽) :=
      decide ((verifier_move.map oracle).sum = claim)

-- we want to test the second round of EXAMPLE B below
def verifier_move {𝔽} [Semiring 𝔽] : List 𝔽  := [0, 1]
noncomputable def test_sumcheck_round_as_IOR {𝔽} [DecidableEq 𝔽] [Semiring 𝔽] (prover : 𝔽 -> (𝔽 → 𝔽) -> Claim 𝔽) (oracle : 𝔽 → 𝔽)  (challenge : 𝔽) : IOR 𝔽  :=
  let claim := prover challenge oracle
  let check := verifier verifier_move claim oracle challenge
  { oracle := oracle,
    verifier_move := verifier_move,
    claim := claim,
    challenge := challenge,
    verifier_check := check }

theorem soundness_IO {𝔽} [DecidableEq 𝔽] [Semiring 𝔽] : ∀ (prover : 𝔽 -> (𝔽 → 𝔽) -> Claim 𝔽) (challenge: 𝔽) (oracle : 𝔽 → 𝔽),
    let claim_from_prover := prover challenge oracle;
    let do_one_round := test_sumcheck_round_as_IOR prover oracle challenge;
    (match claim_from_prover with
    | Claim.scalar c => c = (verifier_move.map oracle).sum
    | Claim.poly inner_round_polynomial =>
     (Polynomial.eval challenge inner_round_polynomial) = (verifier_move.map oracle).sum) ->
    Pr ( do_one_round.verifier_check = True) <= deg(f)/ |F|  := by sorry


  --  Pr[verifier_check == true] <= deg(f)/ |F|


noncomputable def test_sumcheck_round_as_IOR' : IOR (ZMod 19) :=
  test_sumcheck_round_as_IOR (fun _challenge _oracle => test_claim)  test_oracle test_challenge


#simp test_sumcheck_round_as_IOR'.verifier_check

-- if claim == SUM x in {0,1} f(x), Pr[verifier_check == true] == 1
-- else .. claim != SUM x in {0,1} f(x), Pr[verifier_check == true] <= deg(f)/ |F|


-- EXAMPLE A -> why sumcheck over univariate P is useless
-- p = 3*x + 1, true sum = 5 mod 19
-- round 0 prover sums over all points
-- point: [0] --> 1
-- point: [1] --> 4
-- prover interpolates ((0, 1), (1, 4)) and sends g0 = 3*x + 1 <-- this is the original polynomial, so this is not useful for anything
-- verifier checks 1 + 4 = 5
-- protocol transcript { prover_messages: [(1, 4)], verifier_messages: [], is_accepted: true }


-- EXAMPLE B -> sumcheck over multivariate P is useful
-- p = 3*x_0*x_1 + 5*x_0 + 1, true sum = 17 mod 19
-- round 0 prover sums over all points
-- point: [0, 0] -> 1
-- point: [1, 0] -> 6
-- point: [0, 1] -> 1
-- point: [1, 1] -> 9
-- prover interpolates ((0, 2), (1, 15)) and sends univariate g0 = 13*x + 2 <-- g0(0) = 2, g1(1) = 15
-- verifier checks 2 + 15 = 17 mod 19
-- verifier challenge 2
-- round 1 prover sums over smaller points after absorbing verifier challenge
-- point: [2, 0] -> 11
-- point: [2, 1] -> 17
-- prover interpolates ((0, 11), (1, 17)) and sends univariate g1 = 6*x + 11 <-- g0(0) = 11, g1(1) = 17
-- verifier checks 11 + 17 =? g0(2) --> 13*2 + 2 (yes)
-- transcript { prover_messages: [(2, 15), (11, 17)], verifier_messages: [2], is_accepted: true }
