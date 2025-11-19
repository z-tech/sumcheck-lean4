import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.SchwartzZippel

import Mathlib.Data.ZMod.Basic

import Sumcheck.Prover
import Sumcheck.Verifier

noncomputable def absorbX0
  {𝔽} [CommSemiring 𝔽] {n : ℕ}
  (challenge : 𝔽)
  (p : MvPolynomial (Fin (n+1)) 𝔽) :
  MvPolynomial (Fin n) 𝔽 :=
  MvPolynomial.eval₂
    (MvPolynomial.C : 𝔽 →+* MvPolynomial (Fin n) 𝔽)
    (fun i : Fin (n+1) =>
      -- split on whether i = 0 or i = succ j
      Fin.cases
        (MvPolynomial.C challenge)      -- i = 0  ↦ constant polynomial `challenge`
        (fun j => MvPolynomial.X j)     -- i = succ j ↦ variable X j in the smaller index type
        i)
    p

@[simp]
noncomputable def verifier_move {𝔽} [CommRing 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] (claim : 𝔽) (prover_message: Polynomial 𝔽) (simulated_challenge : 𝔽) : (Bool × 𝔽) :=
  let is_accepted := check_round claim prover_message
  (is_accepted, Polynomial.eval simulated_challenge prover_message)

@[simp]
noncomputable def verifier_move' {𝔽} [CommRing 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (prover_message_from_last_round prover_message_this_round : Polynomial 𝔽) (challenge : 𝔽) : Bool :=
  Polynomial.eval challenge prover_message_from_last_round =
                     Polynomial.eval 0 prover_message_this_round + Polynomial.eval 1 prover_message_this_round


@[simp]
noncomputable def prover_move {𝔽} [CommRing 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] (p: MvPolynomial (Fin n) 𝔽) (verifier_challenge: 𝔽) : (Polynomial 𝔽 × MvPolynomial (Fin (n - 1))  𝔽) :=
  match n with
  | 0 => (Polynomial.C 0, MvPolynomial.C 0)
  | Nat.succ m =>
    let challenges : Fin 1 -> 𝔽 := ![verifier_challenge]
    have hcard : 1 ≤ Nat.succ m := Nat.succ_le_succ (Nat.zero_le m)
    let message := generate_prover_message_from_sums (generate_sums_variablewise challenges hcard p 0) (generate_sums_variablewise challenges hcard p 1)
    (message, absorbX0 verifier_challenge p)

@[simp]
noncomputable def polyToMvFin1 {𝔽} [CommSemiring 𝔽]: Polynomial 𝔽 → MvPolynomial (Fin 1) 𝔽 :=
  Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0)

lemma one_round_general {𝔽} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] :
 ∀ (prover_message_from_last_round prover_message_this_round : Polynomial 𝔽),
  prover_message_this_round != 0 ->
  (Finset.filter (fun (challenge : 𝔽) => verifier_move' prover_message_from_last_round prover_message_this_round challenge = true) Finset.univ).card
  ≤ prover_message_this_round.natDegree / ((Finset.univ : Finset 𝔽).card):= by
      unfold verifier_move'
      simp
      intros prover_message_from_last_round prover_message_this_round polyDiffZero
      let interm_poly : Polynomial 𝔽 := prover_message_from_last_round - Polynomial.C (Polynomial.eval 0 prover_message_this_round + Polynomial.eval 1 prover_message_this_round)
      let interm_mvpoly : MvPolynomial (Fin 1) 𝔽 := polyToMvFin1 interm_poly
      have sz := (MvPolynomial.schwartz_zippel_totalDegree (R := 𝔽) (p :=  interm_mvpoly))
      have isNotZero : interm_mvpoly != 0 := by
        unfold interm_mvpoly interm_poly
        simp [*]
        sorry
      simp [*] at isNotZero
      specialize (sz isNotZero Finset.univ)

      ring_nf
      decide
