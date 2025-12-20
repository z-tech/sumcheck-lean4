import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.SchwartzZippel

import Mathlib.Data.ZMod.Basic

import Sumcheck.Prover
import Sumcheck.Verifier
import Sumcheck.Utils

@[simp]
noncomputable def verifier_move {𝔽} [CommRing 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (expected_value : 𝔽)
  (round_polynomial : MvPolynomial (Fin 1) 𝔽)
  (challenge : 𝔽) : Option 𝔽 :=
  if verifier_check expected_value round_polynomial then
    some (verifier_generate_expected_value_next_round round_polynomial challenge)
  else
    none

@[simp]
noncomputable def prover_move {𝔽} [CommRing 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] (p: MvPolynomial (Fin n) 𝔽) (verifier_challenge: 𝔽) : (MvPolynomial (Fin 1) 𝔽 × MvPolynomial (Fin (n - 1))  𝔽) :=
  match n with
  | 0 => (MvPolynomial.C 0, MvPolynomial.C 0)
  | Nat.succ m =>
    let challenges : Fin 1 -> 𝔽 := ![verifier_challenge]
    have hcard : 1 ≤ Nat.succ m := Nat.succ_le_succ (Nat.zero_le m)
    let message := generate_prover_message_from_sums (generate_sums_variablewise challenges hcard p 0) (generate_sums_variablewise challenges hcard p 1)
    (message, absorb_variable_zero verifier_challenge p)



-- lemma one_round_general {𝔽} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] :
--  ∀ (prover_message_from_last_round prover_message_this_round : MvPolynomial (Fin 1) 𝔽),
--   prover_message_this_round != 0 ->
--   (Finset.filter (fun (challenge : 𝔽) => verifier_move prover_message_from_last_round prover_message_this_round challenge = true) Finset.univ).card
--   ≤ prover_message_this_round.totalDegree / ((Finset.univ : Finset 𝔽).card):= by
--       unfold verifier_move
--       simp
--       intros prover_message_from_last_round prover_message_this_round polyDiffZero
--       let interm_poly : MvPolynomial (Fin 1) 𝔽 :=
--         prover_message_from_last_round - MvPolynomial.C (eval_at 0 prover_message_this_round + eval_at 1 prover_message_this_round)
--       have sz := (MvPolynomial.schwartz_zippel_totalDegree (R := 𝔽) (p :=  interm_poly))
--       have isNotZero : interm_poly != 0 := by
--         simp [*]
--         sorry
--       simp [*] at isNotZero
--       specialize (sz isNotZero Finset.univ)

--       ring_nf
--       decide
