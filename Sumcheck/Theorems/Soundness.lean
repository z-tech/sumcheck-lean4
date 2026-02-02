import Sumcheck.Probability.Soundness
import Sumcheck.Lemmas.BadTranscript
import Sumcheck.Lemmas.Accepts
import Sumcheck.Lemmas.Agreement
import Sumcheck.Theorems.SoundnessAux

theorem soundness {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (claim : 𝔽)
  (claim_p : CPoly.CMvPolynomial n 𝔽)
  (adv : Adversary 𝔽 n)
  (h_false_claim : claim ≠ true_sum claim_p) :
    prob_soundness claim claim_p adv
      ≤ n * (max_ind_degree claim_p) / count_field_size (𝔽 := 𝔽) := by
  classical
  dsimp [prob_soundness]

  -- Keep AcceptsAndBad in the per-round event.
  let E : Fin n → (Fin n → 𝔽) → Prop :=
    fun i r =>
      AcceptsAndBadOnChallenges claim claim_p adv r ∧
        RoundDisagreeButAgreeAtChallenge claim claim_p adv r i

  -- Step 1: Accepts∧Bad implies ∃ i, (Accepts∧Bad ∧ RoundDisagreeButAgreeAtChallenge i).
  have hImp :
      ∀ r : (Fin n → 𝔽),
        AcceptsAndBadOnChallenges claim claim_p adv r →
          ∃ i : Fin n, E i r := by
    intro r hAB
    rcases
      accepts_and_bad_implies_exists_round_disagree_but_agree
        (claim := claim) (p := claim_p) (adv := adv) (r := r) hAB
      with ⟨i, hi⟩
    exact ⟨i, ⟨hAB, hi⟩⟩

  have hmono :
      prob_over_challenges (𝔽 := 𝔽) (n := n)
          (fun r => AcceptsAndBadOnChallenges claim claim_p adv r)
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
      ≤ n * (max_ind_degree claim_p) / count_field_size (𝔽 := 𝔽) := by
    simpa [E] using
      sum_accepts_and_round_disagree_but_agree_bound
        (claim := claim) (p := claim_p) (adv := adv)

  exact le_trans (le_trans hmono hunion) hround
