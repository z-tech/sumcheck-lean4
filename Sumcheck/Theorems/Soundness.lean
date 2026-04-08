import Sumcheck.Lemmas.SoundnessLemmas

-- Prob verifier accepts transcript when at least one round poly differs from honest one
theorem soundness {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (domain : List 𝔽)
  (claim : 𝔽)
  (claim_p : CPoly.CMvPolynomial n 𝔽)
  (adv : Adversary 𝔽 n) :
     prob_over_challenges (E := AcceptsAndBadTranscriptOnChallenges domain claim claim_p adv)
      ≤ soundness_error claim_p := by
  classical

  -- Keep AcceptsAndBad in the per-round event.
  let E : Fin n → (Fin n → 𝔽) → Prop :=
    fun i r =>
      AcceptsAndBadTranscriptOnChallenges domain claim claim_p adv r ∧
        RoundDisagreeButAgreeAtChallenge domain claim claim_p adv r i

  -- Step 1: Accepts∧Bad implies ∃ i, (Accepts∧Bad ∧ RoundDisagreeButAgreeAtChallenge i).
  have hImp :
      ∀ r : (Fin n → 𝔽),
        AcceptsAndBadTranscriptOnChallenges domain claim claim_p adv r →
          ∃ i : Fin n, E i r := by
    intro r hAB
    rcases
      accepts_and_bad_implies_exists_round_disagree_but_agree domain
        (claim := claim) (p := claim_p) (adv := adv) (r := r) hAB
      with ⟨i, hi⟩
    exact ⟨i, ⟨hAB, hi⟩⟩

  have hmono :
      prob_over_challenges (𝔽 := 𝔽) (n := n)
          (fun r => AcceptsAndBadTranscriptOnChallenges domain claim claim_p adv r)
        ≤
      prob_over_challenges (𝔽 := 𝔽) (n := n)
          (fun r => ∃ i : Fin n, E i r) :=
    prob_over_challenges_mono (𝔽 := 𝔽) (n := n) hImp

  -- Step 2: union bound over i.
  have hunion :
      prob_over_challenges (𝔽 := 𝔽) (n := n)
          (fun r => ∃ i : Fin n, E i r)
        ≤
      (∑ i : Fin n,
        prob_over_challenges (𝔽 := 𝔽) (n := n)
          (fun r => E i r)) :=
    prob_over_challenges_exists_le_sum (𝔽 := 𝔽) (n := n) E

  -- Step 3: use the (now-lemma) sumcheck-specific bound.
  have hround :
      (∑ i : Fin n,
        prob_over_challenges (𝔽 := 𝔽) (n := n) (fun r => E i r))
      ≤ soundness_error claim_p := by
    simpa [E, soundness_error] using
      sum_accepts_and_round_disagree_but_agree_bound domain
        (claim := claim) (p := claim_p) (adv := adv)

  exact le_trans (le_trans hmono hunion) hround

-- Prob verifier accepts transcript when claim is not honest claim
theorem soundness_dishonest {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (domain : List 𝔽)
  (claim : 𝔽)
  (claim_p : CPoly.CMvPolynomial n 𝔽)
  (adv : Adversary 𝔽 n)
  (h : claim ≠ honest_claim domain (p := claim_p)) :
  prob_over_challenges (E := AcceptsOnChallenges domain claim claim_p adv)
    ≤ soundness_error claim_p := by
  classical

  -- Key reduction: dishonest claim ⇒ (accept → bad), hence accept ⊆ (accept ∧ bad).
  have hImp :
      ∀ r : (Fin n → 𝔽),
        AcceptsOnChallenges domain claim claim_p adv r →
          AcceptsAndBadTranscriptOnChallenges domain claim claim_p adv r := by
    intro r hAcc
    refine ⟨?hAccEvent, ?hBad⟩
    · -- acceptance part
      simpa [AcceptsOnChallenges, AcceptsAndBadTranscriptOnChallenges] using hAcc
    · -- badness part
      exact
        accepts_on_challenges_dishonest_implies_bad domain
          (claim := claim) (p := claim_p) (adv := adv) (r := r) h hAcc

  have hmono :
      prob_over_challenges (𝔽 := 𝔽) (n := n)
          (fun r => AcceptsOnChallenges domain claim claim_p adv r)
        ≤
      prob_over_challenges (𝔽 := 𝔽) (n := n)
          (fun r => AcceptsAndBadTranscriptOnChallenges domain claim claim_p adv r) :=
    prob_over_challenges_mono (𝔽 := 𝔽) (n := n) hImp

  -- Now just reuse your existing soundness_accept_bad_transcript theorem.
  have hsound :
      prob_over_challenges (𝔽 := 𝔽) (n := n)
          (fun r => AcceptsAndBadTranscriptOnChallenges domain claim claim_p adv r)
        ≤ soundness_error claim_p :=
    soundness domain (𝔽 := 𝔽) (n := n) (claim := claim) (claim_p := claim_p) (adv := adv)

  exact le_trans hmono hsound
