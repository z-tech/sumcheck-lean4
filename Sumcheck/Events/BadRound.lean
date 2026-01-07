import CompPoly.CMvPolynomial

import Sumcheck.Models.Adversary
import Sumcheck.Models.AdversaryTranscript

def honest_round_poly
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽)
  (ch : Fin n → 𝔽)
  (i : Fin n) : CPoly.CMvPolynomial 1 𝔽 :=
  honest_prover_message (n := n) (k := i.val) p (challenge_subset ch i) (Nat.succ_le_of_lt i.isLt)

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
