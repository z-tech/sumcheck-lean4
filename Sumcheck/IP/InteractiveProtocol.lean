import InteractiveProtocol.Src.Protocol
import InteractiveProtocol.Properties.Soundness
import Sumcheck.Src
import Sumcheck.Properties.Theorems
import Sumcheck.Properties.Events
import Sumcheck.Properties.Models
import Sumcheck.Properties.Probability

-- Here we map sumcheck into the interface for public coin interactive protocols
-- the intention is to show how completeness and soundness of the IP lift into the framework

-- this bundles domain, claim and claim_polynomial
structure SumcheckStatement (𝔽 : Type) [Field 𝔽] [DecidableEq 𝔽] (n : ℕ) where
  domain : List 𝔽
  claim : 𝔽
  polynomial : CPoly.CMvPolynomial n 𝔽

-- need predicate so we can quantify over false/ true statements
def sumcheckClaimIsCorrect {𝔽 : Type} {n : ℕ} [Field 𝔽] [DecidableEq 𝔽]
    (st : SumcheckStatement 𝔽 n) : Prop :=
  st.claim = honest_claim st.domain st.polynomial

/-- The sumcheck protocol as a `PublicCoinProtocol`. -/
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

/-- Convert a generic `Prover` to an old-style `Adversary` relative to a statement. -/
def proverToAdversary {𝔽 : Type} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n)))
    (st : SumcheckStatement 𝔽 n) : Adversary 𝔽 n :=
  fun _p _claim i chs => P.respond st i chs

/-- The honest sumcheck prover as a generic `Prover`. -/
def sumcheckHonestProver {𝔽 : Type} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] :
    Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n)) where
  respond := fun st i chs =>
    honest_prover_message_at st.domain st.polynomial i chs

/-! ## Bridge Lemmas -/

/-- Bridge between `probEvent` and `prob_over_challenges`. -/
lemma probEvent_eq_prob_over_challenges' {𝔽 : Type} {n : ℕ} [Fintype 𝔽]
    (E : (Fin n → 𝔽) → Prop) :
    @probEvent 𝔽 n _ E = prob_over_challenges E := by
  simp only [probEvent, prob_over_challenges, allChallenges, all_assignments_n]

/-- The acceptance event in the generic framework matches the old one,
    for any prover/adversary that produces the same messages. -/
lemma sumcheck_verifier_accepts_eq {𝔽 : Type} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (st : SumcheckStatement 𝔽 n)
    (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n)))
    (r : Fin n → 𝔽) :
    sumcheckProtocol.verifier_accepts st
      (generateTranscript sumcheckProtocol st P r)
    = (is_verifier_accepts_transcript st.domain st.polynomial
        { round_polys := fun i => P.respond st i (challenge_subset r i)
          challenges := r
          claims := generate_honest_claims st.claim
            (fun i => P.respond st i (challenge_subset r i)) r } = true) := by
  rfl

/-! ## Main Theorems -/

/-- **Sumcheck Soundness** in the generic framework. -/
theorem sumcheck_hasSoundnessError {𝔽 : Type} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] :
    hasSoundnessError
      (sumcheckProtocol (𝔽 := 𝔽) (n := n))
      sumcheckClaimIsCorrect
      (fun st => soundness_error st.polynomial) := by
  intro st P hFalse
  unfold probAccept
  set adv : Adversary 𝔽 n := proverToAdversary P st with hadv
  -- Bridge the events
  have hEq : (fun r => sumcheckProtocol.verifier_accepts st
      (generateTranscript sumcheckProtocol st P r))
    = (fun r => AcceptsOnChallenges st.domain st.claim st.polynomial adv r) := by
    ext r
    simp only [sumcheck_verifier_accepts_eq, AcceptsOnChallenges, AcceptsEvent,
               AdversaryTranscript, proverToAdversary, hadv]
  rw [hEq, probEvent_eq_prob_over_challenges']
  have hClaim : st.claim ≠ honest_claim st.domain st.polynomial := by
    unfold sumcheckClaimIsCorrect at hFalse; exact hFalse
  exact soundness_dishonest st.domain st.claim st.polynomial adv hClaim

/-- **Sumcheck Perfect Completeness** in the generic framework. -/
theorem sumcheck_hasPerfectCompleteness {𝔽 : Type} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] :
    hasPerfectCompleteness
      (sumcheckProtocol (𝔽 := 𝔽) (n := n))
      sumcheckClaimIsCorrect
      sumcheckHonestProver := by
  intro st hTrue
  unfold probAccept
  -- Bridge the events
  have hEq : (fun r => sumcheckProtocol.verifier_accepts st
      (generateTranscript sumcheckProtocol st sumcheckHonestProver r))
    = (fun r => AcceptsEvent st.domain st.polynomial
        (generate_honest_transcript st.domain st.polynomial st.claim r)) := by
    ext r
    simp only [sumcheck_verifier_accepts_eq, sumcheckHonestProver,
               AcceptsEvent, generate_honest_transcript,
               honest_prover_message]
  rw [hEq, probEvent_eq_prob_over_challenges']
  rw [hTrue]
  exact perfect_completeness st.domain st.polynomial
