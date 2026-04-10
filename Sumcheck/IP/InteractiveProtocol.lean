import Sumcheck.IP.Statement
import InteractiveProtocol.Properties.Soundness
import Sumcheck.Properties.Theorems
import Sumcheck.Properties.Events
import Sumcheck.Properties.Probability

-- Here we show how sumcheck's completeness and soundness lift into the IP framework

-- the "verifier_accepts" in the IP interface is the same as sumcheck's
-- is_verifier_accepts_transcript function
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

theorem sumcheck_hasSoundnessError {𝔽 : Type} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] :
    hasSoundnessError
      (sumcheckProtocol (𝔽 := 𝔽) (n := n))
      sumcheckClaimIsCorrect
      (fun st => soundness_error st.polynomial) := by
  intro st P hFalse
  unfold probAccept
  have hEq : (fun r => sumcheckProtocol.verifier_accepts st
      (generateTranscript sumcheckProtocol st P r))
    = (fun r => AcceptsOnChallenges st P r) := by
    ext r
    simp only [sumcheck_verifier_accepts_eq, AcceptsOnChallenges, AcceptsEvent, proverTranscript]
  rw [hEq]
  have hClaim : st.claim ≠ honest_claim st.domain st.polynomial := by
    unfold sumcheckClaimIsCorrect at hFalse; exact hFalse
  exact soundness_dishonest st P hClaim

theorem sumcheck_hasPerfectCompleteness {𝔽 : Type} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] :
    hasPerfectCompleteness
      (sumcheckProtocol (𝔽 := 𝔽) (n := n))
      sumcheckClaimIsCorrect
      sumcheckHonestProver := by
  intro st hTrue
  unfold probAccept
  have hEq : (fun r => sumcheckProtocol.verifier_accepts st
      (generateTranscript sumcheckProtocol st sumcheckHonestProver r))
    = (fun r => AcceptsEvent st.domain st.polynomial
        (generate_honest_transcript st.domain st.polynomial st.claim r)) := by
    ext r
    simp only [sumcheck_verifier_accepts_eq, sumcheckHonestProver,
               AcceptsEvent, generate_honest_transcript,
               honest_prover_message]
  rw [hEq]
  rw [hTrue]
  exact perfect_completeness st.domain st.polynomial
