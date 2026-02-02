import CompPoly.CMvPolynomial

import Sumcheck.Models.Adversary
import Sumcheck.Models.AdversaryTranscript

def honest_round_poly
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽)
  (ch : Fin n → 𝔽)
  (i : Fin n) : CPoly.CMvPolynomial 1 𝔽 :=
  honest_prover_message_at (p := p) (i := i) (challenges := challenge_subset ch i)

def honest_round_fun
  {𝔽 : Type _} {n : ℕ}
  [CommRing 𝔽] [DecidableEq 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽)
  (r : Fin n → 𝔽)
  (i : Fin n) : 𝔽 → 𝔽 :=
fun a =>
  round_sum (num_challenges := i.val) (num_vars := n)
    (challenge_subset r i) a p (Nat.succ_le_of_lt i.isLt)

def BadRound
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (round_poly: CPoly.CMvPolynomial 1 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (challenges : Fin n → 𝔽)
  (round_num : Fin n) : Prop :=
  round_poly ≠ honest_round_poly p challenges round_num

def FirstBadRound
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (claim : 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (adversary : Adversary 𝔽 n)
  (r : Fin n → 𝔽) : Prop :=
  ∃ i : Fin n,
    (AdversaryTranscript claim p adversary r).round_polys i
      ≠ honest_round_poly (p := p) (ch := r) i
    ∧
    ∀ j : Fin i.val,
      (AdversaryTranscript claim p adversary r).round_polys ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩
        = honest_round_poly p r ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩

def LastBadRound
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (claim : 𝔽) (p : CPoly.CMvPolynomial n 𝔽) (adv : Adversary 𝔽 n) (r : Fin n → 𝔽) : Prop :=
  ∃ i : Fin n,
    (AdversaryTranscript claim p adv r).round_polys i ≠ honest_round_poly p r i
    ∧
    ∀ j : Fin n, i < j →
      (AdversaryTranscript claim p adv r).round_polys j = honest_round_poly p r j

def RoundDisagreeButAgreeAtChallenge
{𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
(claim : 𝔽) (p : CPoly.CMvPolynomial n 𝔽) (adv : Adversary 𝔽 n)
(r : Fin n → 𝔽) (i : Fin n) : Prop :=
  let t : Transcript 𝔽 n := AdversaryTranscript claim p adv r
  t.round_polys i ≠ honest_round_poly (p := p) (ch := r) i
    ∧ next_claim (𝔽 := 𝔽) (round_challenge := r i) (t.round_polys i)
        = next_claim (𝔽 := 𝔽) (round_challenge := r i) (honest_round_poly (p := p) (ch := r) i)
