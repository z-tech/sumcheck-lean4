import Sumcheck.Probability.Soundness
import Sumcheck.Lemmas.BadTranscript
import Sumcheck.Lemmas.Accepts
import Sumcheck.Lemmas.Agreement
import Sumcheck.Theorems.SoundnessAux

theorem soundness
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (claim : 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (adv : Adversary 𝔽 n)
  (hfalse : claim ≠ true_sum (𝔽 := 𝔽) p) :
  prob_soundness (𝔽 := 𝔽) (n := n) claim p adv
    ≤ n * (max_ind_degree p) / count_field_size (𝔽 := 𝔽) := by
  classical
  -- Unfold the definition: soundness is the probability over challenges of `Accepts ∧ BadTranscript`.
  dsimp [prob_soundness]
  -- Step 1: show that `Accepts ∧ BadTranscript` implies there is some round `i` where the prover's
  -- round polynomial differs from the honest one, yet they agree at the verifier's random challenge.
  have hImp :
      ∀ r : (Fin n → 𝔽),
        AcceptsAndBadOnChallenges claim p adv r →
          ∃ i : Fin n,
            RoundDisagreeButAgreeAtChallenge claim p adv r i := by
    intro r h
    exact accepts_and_bad_implies_exists_round_disagree_but_agree (claim := claim) (p := p) (adv := adv)
      (r := r) hfalse h

  -- Step 2: monotonicity + union bound + per-round Schwartz–Zippel.
  -- First, reduce the probability of `Accepts∧Bad` to the probability of the existential.
  have hmono :
      prob_over_challenges (𝔽 := 𝔽) (n := n)
          (fun r => AcceptsAndBadOnChallenges claim p adv r)
        ≤
      prob_over_challenges (𝔽 := 𝔽) (n := n)
          (fun r => ∃ i : Fin n, RoundDisagreeButAgreeAtChallenge claim p adv r i) :=
    prob_over_challenges_mono (𝔽 := 𝔽) (n := n) hImp

  -- Apply union bound over the `n` possible rounds.
  have hunion :
      prob_over_challenges (𝔽 := 𝔽) (n := n)
          (fun r => ∃ i : Fin n, RoundDisagreeButAgreeAtChallenge claim p adv r i)
        ≤
      (∑ i : Fin n,
        prob_over_challenges (𝔽 := 𝔽) (n := n)
          (fun r => RoundDisagreeButAgreeAtChallenge claim p adv r i)) :=
    prob_over_challenges_exists_le_sum (𝔽 := 𝔽) (n := n)
      (fun i r => RoundDisagreeButAgreeAtChallenge claim p adv r i)

  -- Bound each summand using Schwartz–Zippel (in one variable) and the degree bound `max_ind_degree`.
  have hround :
      (∑ i : Fin n,
        prob_over_challenges (𝔽 := 𝔽) (n := n)
          (fun r => RoundDisagreeButAgreeAtChallenge claim p adv r i))
        ≤
      n * (max_ind_degree p) / count_field_size (𝔽 := 𝔽) := by
    simpa using sum_round_disagree_but_agree_bound (claim := claim) (p := p) (adv := adv)

  exact le_trans (le_trans hmono hunion) hround
