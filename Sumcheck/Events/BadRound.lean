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

def BadRound
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (round_poly: CPoly.CMvPolynomial 1 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (challenges : Fin n → 𝔽)
  (round_num : Fin n) : Prop :=
  round_poly ≠ honest_round_poly p challenges round_num

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
