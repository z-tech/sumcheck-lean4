import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.ZMod.Basic

import Sumcheck.Prover
import Sumcheck.Verifier

-- @[simp]
-- noncomputable def do_round {𝔽} [CommRing 𝔽] [DecidableEq 𝔽]
-- (claim : 𝔽) (prover_message : Polynomial 𝔽) : Bool :=
--   decide (Polynomial.eval 0 prover_message + Polynomial.eval 1 prover_message = claim)
