import Sumcheck.Properties.Probability.Challenges
import Sumcheck.Properties.Lemmas.HonestRoundProofs
import Sumcheck.Properties.Lemmas.Degree
import Sumcheck.Properties.Lemmas.Accepts
import Sumcheck.Properties.Lemmas.SoundnessLemmas

-- Prob verifier accepts when all round polys are honest (and claim is honest) is one
theorem perfect_completeness
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽) :
  prob_over_challenges (𝔽 := 𝔽) (n := n)
    (fun r =>
      AcceptsEvent (𝔽 := 𝔽) (n := n) domain p (honest_claim domain p)
        (generate_honest_transcript (𝔽 := 𝔽) (n := n) domain p (honest_claim domain p) r))
  = 1 := by
  classical
  -- the honest transcript is accepted for every challenge tuple.

  -- First, prove every honest transcript is accepted
  have hE : ∀ r : Fin n → 𝔽,
      AcceptsEvent domain p (honest_claim domain p) (generate_honest_transcript domain p (honest_claim domain p) r) := by
    intro r
    simp only [AcceptsEvent, is_verifier_accepts, Transcript.claims, Bool.and_eq_true]
    constructor
    · -- rounds_ok: each round passes verifier_check and claims consistency
      rw [List.all_eq_true]
      intro i _
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · -- verifier_check passes
        simp only [verifier_check, Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · -- Sum identity: domain sum of honest poly = claim
          exact honest_transcript_sum_identity domain p r i
        · -- Degree bound: honest_round_poly degree ≤ ind_degree_k
          -- The honest polynomial has degree at most the individual degree
          have hpoly : (generate_honest_transcript domain p (honest_claim domain p) r).round_polys i =
            honest_round_poly domain p r i := by
            simp [generate_honest_transcript, honest_round_poly, honest_prover_message_at]
          rw [hpoly]
          exact honest_round_poly_degree_le_ind_degree_k domain p r i
      · -- Claims consistency: claims i.succ = next_claim (challenges i) (round_polys i)
        -- For i : Fin n, i.succ = ⟨i.val + 1, ...⟩ which matches the succ case of generate_honest_claims
        have hsuc : i.succ = ⟨i.val.succ, Nat.succ_lt_succ i.isLt⟩ := Fin.ext rfl
        simp only [generate_honest_transcript, generate_honest_claims, next_claim, hsuc]
    · -- final_ok: final claim equals polynomial evaluation
      simp only [decide_eq_true_eq]
      -- Use the helper lemma that handles dependent types via induction
      exact honest_transcript_final_eq_eval n domain p r
  have hfilter :
      (Finset.univ.filter (fun r => AcceptsEvent domain p (honest_claim domain p) (generate_honest_transcript domain p (honest_claim domain p) r)) : Finset (Fin n → 𝔽))
        = Finset.univ := by
    ext r
    simp [hE r]

  simp [probEvent, allChallenges, hfilter]
