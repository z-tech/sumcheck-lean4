import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Data.ZMod.Basic

open Polynomial

inductive Claim (𝔽 : Type) [Semiring 𝔽]
  | scalar : 𝔽 → Claim 𝔽
  | poly   : Polynomial 𝔽 → Claim 𝔽

structure IOR (𝔽 : Type)  [Semiring 𝔽] where
  oracle: 𝔽 → 𝔽
  verifier_move : List 𝔽
  verifier_check : Bool
  claim : Claim 𝔽
  challenge: 𝔽

noncomputable def test_polynomial : Polynomial (ZMod 7) := X ^ 2 + 1
noncomputable def test_oracle : (ZMod 7) → (ZMod 7) := λ x => Polynomial.eval x test_polynomial
noncomputable def test_claim : Claim (ZMod 7) := Claim.scalar (5 : ZMod 7)
noncomputable def test_challenge := (3: ZMod 7)
noncomputable def test_sumcheck_round_as_IOR : IOR (ZMod 7) :=
  let oracle := test_oracle
  let verifier_move := [0, 1]
  let claim := test_claim
  let challenge := test_challenge
  let check :=
    match claim with
    | Claim.scalar first_round_claim =>
        decide ((verifier_move.map oracle).sum = first_round_claim)
    | Claim.poly inner_round_polynomial =>
        decide ((verifier_move.map oracle).sum = Polynomial.eval challenge inner_round_polynomial)
  { oracle := oracle,
    verifier_move := verifier_move,
    claim := claim,
    challenge := challenge,
    verifier_check := check }

#reduce test_sumcheck_round_as_IOR.verifier_check
