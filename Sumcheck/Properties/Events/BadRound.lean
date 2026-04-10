import CompPoly.Multivariate.CMvPolynomial

import Sumcheck.IP.Statement

def honest_round_poly
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (ch : Fin n → 𝔽)
  (i : Fin n) : CPoly.CMvPolynomial 1 𝔽 :=
  honest_prover_message_at (domain := domain) (p := p) (i := i) (challenges := challenge_subset ch i)

def BadRound
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (domain : List 𝔽)
  (round_poly: CPoly.CMvPolynomial 1 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (challenges : Fin n → 𝔽)
  (round_num : Fin n) : Prop :=
  round_poly ≠ honest_round_poly domain p challenges round_num

def LastBadRound
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (st : SumcheckStatement 𝔽 n)
  (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n)))
  (r : Fin n → 𝔽) : Prop :=
  let t := proverTranscript st P r
  ∃ i : Fin n,
    t.round_polys i ≠ honest_round_poly st.domain st.polynomial r i
    ∧
    ∀ j : Fin n, i < j →
      t.round_polys j = honest_round_poly st.domain st.polynomial r j

def RoundDisagreeButAgreeAtChallenge
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (st : SumcheckStatement 𝔽 n)
  (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n)))
  (r : Fin n → 𝔽) (i : Fin n) : Prop :=
  let t := proverTranscript st P r
  t.round_polys i ≠ honest_round_poly (domain := st.domain) (p := st.polynomial) (ch := r) i
    ∧ next_claim (𝔽 := 𝔽) (round_challenge := r i) (t.round_polys i)
        = next_claim (𝔽 := 𝔽) (round_challenge := r i)
          (honest_round_poly (domain := st.domain) (p := st.polynomial) (ch := r) i)
