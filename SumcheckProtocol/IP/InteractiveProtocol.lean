import SumcheckProtocol.IP.Statement
import InteractiveProtocol.Properties.Soundness
import SumcheckProtocol.Properties.Theorems
import SumcheckProtocol.Properties.Events
import SumcheckProtocol.Properties.Probability

-- Here we show how sumcheck's completeness and soundness lift into the IP framework

/-- **Partial-run sumcheck soundness in the IP framework.** For any `k : Fin (n+1)`,
the partial-run sumcheck protocol satisfies `hasSoundnessError` with bound
`soundnessErrorK k st.polynomial = k.val · maxIndDegree(p) / |𝔽|`. -/
theorem sumcheck_hasSoundnessError_k {𝔽 : Type*} {n : ℕ}
    [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] (k : Fin (n + 1)) :
    hasSoundnessError
      (sumcheckProtocol (𝔽 := 𝔽) (n := n) k)
      sumcheckClaimIsCorrect
      (fun st => soundnessErrorK k st.polynomial) := by
  intro st P hFalse
  unfold probAccept
  have hEq : (fun r => (sumcheckProtocol k).verifierAccepts st
      (generateTranscript (sumcheckProtocol k) st P r))
    = (fun r => AcceptsOnChallenges k st P r) := rfl
  rw [hEq]
  exact soundness_dishonest_k k st P
    (by unfold sumcheckClaimIsCorrect at hFalse; exact hFalse)

/-- **Partial-run sumcheck perfect completeness in the IP framework.** For any
`k : Fin (n+1)`, the partial-run sumcheck protocol with the partial-run
honest prover `sumcheckHonestProver k` satisfies `hasPerfectCompleteness`. -/
theorem sumcheck_hasPerfectCompleteness_k {𝔽 : Type*} {n : ℕ}
    [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] (k : Fin (n + 1)) :
    hasPerfectCompleteness
      (sumcheckProtocol (𝔽 := 𝔽) (n := n) k)
      sumcheckClaimIsCorrect
      (sumcheckHonestProver k) := by
  intro st hTrue
  unfold probAccept
  have hEq : (fun r => (sumcheckProtocol k).verifierAccepts st
      (generateTranscript (sumcheckProtocol k) st (sumcheckHonestProver k) r))
    = (fun r => AcceptsOnChallenges k st (sumcheckHonestProver k) r) := rfl
  rw [hEq]
  exact perfect_completeness_k k st
    (by unfold sumcheckClaimIsCorrect at hTrue; exact hTrue)

/-- Full-run specialisation of `sumcheck_hasSoundnessError_k` at `k = ⟨n, _⟩`. -/
theorem sumcheck_hasSoundnessError {𝔽 : Type*} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] :
    hasSoundnessError
      (sumcheckProtocol (𝔽 := 𝔽) (n := n) ⟨n, Nat.lt_succ_self n⟩)
      sumcheckClaimIsCorrect
      (fun st => soundnessError st.polynomial) := by
  have h := sumcheck_hasSoundnessError_k (𝔽 := 𝔽) (n := n) ⟨n, Nat.lt_succ_self n⟩
  intro st P hFalse
  have hk := h st P hFalse
  simpa [soundnessError, soundnessErrorK] using hk

/-- Full-run specialisation of `sumcheck_hasPerfectCompleteness_k` at `k = ⟨n, _⟩`. -/
theorem sumcheck_hasPerfectCompleteness {𝔽 : Type*} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] :
    hasPerfectCompleteness
      (sumcheckProtocol (𝔽 := 𝔽) (n := n) ⟨n, Nat.lt_succ_self n⟩)
      sumcheckClaimIsCorrect
      (sumcheckHonestProver ⟨n, Nat.lt_succ_self n⟩) :=
  sumcheck_hasPerfectCompleteness_k (𝔽 := 𝔽) (n := n) ⟨n, Nat.lt_succ_self n⟩
