import InteractiveProtocol.Src.Protocol
import Sumcheck.Src

-- this bundles domain, claim and claim_polynomial
structure SumcheckStatement (𝔽 : Type) [Field 𝔽] [DecidableEq 𝔽] (n : ℕ) where
  domain : List 𝔽
  claim : 𝔽
  polynomial : CPoly.CMvPolynomial n 𝔽

-- need predicate so we can quantify over false/ true statements
def sumcheckClaimIsCorrect {𝔽 : Type} {n : ℕ} [Field 𝔽] [DecidableEq 𝔽]
    (st : SumcheckStatement 𝔽 n) : Prop :=
  st.claim = honest_claim st.domain st.polynomial

-- this is the actual mapping into the framework
def sumcheckProtocol {𝔽 : Type} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] :
    PublicCoinProtocol (SumcheckStatement 𝔽 n) 𝔽 n where
  ProverMessage := fun _ => CPoly.CMvPolynomial 1 𝔽
  Transcript := (Fin n → CPoly.CMvPolynomial 1 𝔽) × (Fin n → 𝔽)
  mkTranscript := fun msgs chs => (msgs, chs)
  challenges := fun tr => tr.2
  proverMessage := fun tr i => tr.1 i
  verifier_accepts := fun st tr =>
    is_verifier_accepts_transcript st.domain st.polynomial
      { round_polys := tr.1
        challenges := tr.2
        claims := generate_honest_claims st.claim tr.1 tr.2 } = true
  verifier_decides := fun _ _ => inferInstance
  challenges_mk := fun _ _ => rfl
  proverMessage_mk := fun _ _ _ => rfl

-- the honest sumcheck prover as a generic Prover
def sumcheckHonestProver {𝔽 : Type} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] :
    Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n)) where
  respond := fun st i chs =>
    honest_prover_message_at st.domain st.polynomial i chs

-- construct a Transcript from a Prover and challenges
-- this is the sumcheck-specific analogue of generateTranscript that
-- produces the old Transcript type (with claims)
def proverTranscript
    {𝔽 : Type} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (st : SumcheckStatement 𝔽 n)
    (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n)))
    (r : Fin n → 𝔽) : Transcript 𝔽 n :=
  let round_polys : Fin n → CPoly.CMvPolynomial 1 𝔽 :=
    fun i => P.respond st i (challenge_subset r i)
  { round_polys := round_polys
    challenges := r
    claims := generate_honest_claims st.claim round_polys r }

@[simp] lemma proverTranscript_challenges
    {𝔽 : Type} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (st : SumcheckStatement 𝔽 n)
    (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n)))
    (r : Fin n → 𝔽) :
    (proverTranscript st P r).challenges = r := rfl

@[simp] lemma proverTranscript_round_polys
    {𝔽 : Type} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (st : SumcheckStatement 𝔽 n)
    (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n)))
    (r : Fin n → 𝔽) (i : Fin n) :
    (proverTranscript st P r).round_polys i = P.respond st i (challenge_subset r i) := rfl
