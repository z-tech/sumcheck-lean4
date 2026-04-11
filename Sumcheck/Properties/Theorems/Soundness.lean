import Sumcheck.Properties.Lemmas.SoundnessLemmas

-- Prob verifier accepts transcript when at least one round poly differs from honest one
theorem soundness {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (st : SumcheckStatement 𝔽 n)
  (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n))) :
     prob_over_challenges (E := AcceptsAndBadTranscriptOnChallenges st P)
      ≤ soundness_error st.polynomial := by
  classical

  -- Keep AcceptsAndBad in the per-round event.
  let E : Fin n → (Fin n → 𝔽) → Prop :=
    fun i r =>
      AcceptsAndBadTranscriptOnChallenges st P r ∧
        RoundDisagreeButAgreeAtChallenge st P r i

  -- Step 1: Accepts∧Bad implies ∃ i, (Accepts∧Bad ∧ RoundDisagreeButAgreeAtChallenge i).
  have hImp :
      ∀ r : (Fin n → 𝔽),
        AcceptsAndBadTranscriptOnChallenges st P r →
          ∃ i : Fin n, E i r := by
    intro r hAB
    rcases
      accepts_and_bad_implies_exists_round_disagree_but_agree
        (st := st) (P := P) (r := r) hAB
      with ⟨i, hi⟩
    exact ⟨i, ⟨hAB, hi⟩⟩

  have hmono :
      prob_over_challenges (𝔽 := 𝔽) (n := n)
          (fun r => AcceptsAndBadTranscriptOnChallenges st P r)
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
      ≤ soundness_error st.polynomial := by
    simpa [E, soundness_error] using
      sum_accepts_and_round_disagree_but_agree_bound
        (st := st) (P := P)

  exact le_trans (le_trans hmono hunion) hround

-- Prob verifier accepts transcript when claim is not honest claim
theorem soundness_dishonest {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (st : SumcheckStatement 𝔽 n)
  (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n)))
  (h : st.claim ≠ honest_claim st.domain (p := st.polynomial)) :
  prob_over_challenges (E := AcceptsOnChallenges st P)
    ≤ soundness_error st.polynomial := by
  classical

  -- Key reduction: dishonest claim ⇒ (accept → bad), hence accept ⊆ (accept ∧ bad).
  have hImp :
      ∀ r : (Fin n → 𝔽),
        AcceptsOnChallenges st P r →
          AcceptsAndBadTranscriptOnChallenges st P r := by
    intro r hAcc
    refine ⟨?hAccEvent, ?hBad⟩
    · -- acceptance part
      simpa [AcceptsOnChallenges, AcceptsAndBadTranscriptOnChallenges] using hAcc
    · -- badness part
      exact
        accepts_on_challenges_dishonest_implies_bad
          (st := st) (P := P) (r := r) h hAcc

  have hmono :
      prob_over_challenges (𝔽 := 𝔽) (n := n)
          (fun r => AcceptsOnChallenges st P r)
        ≤
      prob_over_challenges (𝔽 := 𝔽) (n := n)
          (fun r => AcceptsAndBadTranscriptOnChallenges st P r) :=
    prob_over_challenges_mono (𝔽 := 𝔽) (n := n) hImp

  -- Now just reuse your existing soundness_accept_bad_transcript theorem.
  have hsound :
      prob_over_challenges (𝔽 := 𝔽) (n := n)
          (fun r => AcceptsAndBadTranscriptOnChallenges st P r)
        ≤ soundness_error st.polynomial :=
    soundness (𝔽 := 𝔽) (n := n) (st := st) (P := P)

  exact le_trans hmono hsound
