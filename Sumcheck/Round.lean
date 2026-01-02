import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Data.ZMod.Basic

import Mathlib.Data.Fintype.Card
import Mathlib

import CompPoly
import CompPoly.CMvPolynomial
import CompPoly.CMvMonomial
import CompPoly.Lawful

import Sumcheck.Prover
import Sumcheck.Verifier
import Sumcheck.Polynomials

open scoped BigOperators

@[simp]
def verifier_move {𝔽} [CommRing 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (expected_value : 𝔽)
  (round_polynomial : CPoly.CMvPolynomial 1 𝔽)
  (challenge : 𝔽) : Option 𝔽 :=
  if verifier_check expected_value round_polynomial then
    some (verifier_generate_expected_value_next_round round_polynomial challenge)
  else
    none

@[simp]
def prover_move
  {𝔽} [CommRing 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (n : ℕ)
  (h : n > 0)
  (p : CPoly.CMvPolynomial n 𝔽)
  (verifier_challenge : 𝔽) :
  (CPoly.CMvPolynomial 1 𝔽 × CPoly.CMvPolynomial (n - 1) 𝔽) :=
by
  cases n with
  | zero =>
      -- n = 0
      exact (CPoly.Lawful.C (n := 1) (R := 𝔽) 0,
             CPoly.Lawful.C (n := 0) (R := 𝔽) 0)
  | succ m =>
      -- n = m+1
      have hcard : (0 : ℕ) + 1 ≤ m + 1 := by
        simp

      let sum0 := sum_over_boolean_extension ![] 0 p hcard
      let sum1 := sum_over_boolean_extension ![] 1 p hcard

      let message := generate_prover_message_from_sums sum0 sum1
      exact (message, absorb_variable_zero (n := m) verifier_challenge p)


-- probability that a uniformly random challenge makes q evaluate to zero
lemma prob_root
  {𝔽} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (q : CPoly.CMvPolynomial 1 𝔽)
  (hq : q ≠ 0) :
  (↑{f ∈ Fintype.piFinset (fun _ : Fin 1 => (Finset.univ : Finset 𝔽))
        | q.eval f = 0}.card : ℚ)
    / (Fintype.card 𝔽 : ℚ)
  ≤ (q.totalDegree : ℚ) / (Fintype.card 𝔽 : ℚ) := by
  -- transport nonzero across the equivalence
  have hq' : CPoly.fromCMvPolynomial q ≠ (0 : MvPolynomial (Fin 1) 𝔽) := by
    intro h
    apply hq
    -- use your equivalence lemma: q = 0 ↔ from q = from 0
    have : CPoly.fromCMvPolynomial q = CPoly.fromCMvPolynomial (0 : CPoly.CMvPolynomial 1 𝔽) := by
      simpa [CPoly.map_zero] using h
    exact (CPoly.eq_iff_fromCMvPolynomial (u := q) (v := 0)).2 this

  -- Schwartz–Zippel on the MvPolynomial image
  have sz :=
    MvPolynomial.schwartz_zippel_totalDegree
      (R := 𝔽)
      (p := CPoly.fromCMvPolynomial q)
      hq'
      (S := (Finset.univ : Finset 𝔽))

  -- rewrite eval/degree back to CMvPolynomial using your `*_equiv` lemmas
  -- and simplify the n = 1 denominator
  simpa [CPoly.eval_equiv (p := q), CPoly.totalDegree_equiv (p := q), pow_one] using sz


-- probability the sampled challenge causes the verifier to accept when message != honest


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
