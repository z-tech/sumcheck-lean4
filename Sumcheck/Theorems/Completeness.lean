import Sumcheck.Probability.Challenges
import Sumcheck.Lemmas.HonestRoundProofs
import Sumcheck.Lemmas.Degree
import Sumcheck.Lemmas.Accepts
import Sumcheck.Lemmas.SoundnessLemmas


theorem perfect_completeness
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽) :
  prob_over_challenges (𝔽 := 𝔽) (n := n)
    (fun r =>
      AcceptsEvent (𝔽 := 𝔽) (n := n) p
        (generate_honest_transcript (𝔽 := 𝔽) (n := n) p (true_sum p) r))
  = 1 := by
  classical
  -- the honest transcript is accepted for every challenge tuple.

  -- First, prove every honest transcript is accepted
  have hE : ∀ r : Fin n → 𝔽,
      AcceptsEvent p (generate_honest_transcript p (true_sum p) r) := by
    intro r
    simp only [AcceptsEvent, is_verifier_accepts_transcript, Bool.and_eq_true]
    constructor
    · -- rounds_ok: each round passes verifier_check and claims consistency
      rw [List.all_eq_true]
      intro i _
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · -- verifier_check passes
        simp only [verifier_check, Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · -- Sum identity: eval at 0 + eval at 1 = claim
          exact honest_transcript_sum_identity p r i
        · -- Degree bound: honest_round_poly degree ≤ ind_degree_k
          -- The honest polynomial has degree at most the individual degree
          have hpoly : (generate_honest_transcript p (true_sum p) r).round_polys i =
            honest_round_poly p r i := by
            simp [generate_honest_transcript, honest_round_poly, honest_prover_message]
          rw [hpoly]
          exact honest_round_poly_degree_le_ind_degree_k p r i
      · -- Claims consistency: claims i.succ = next_claim (challenges i) (round_polys i)
        -- For i : Fin n, i.succ = ⟨i.val + 1, ...⟩ which matches the succ case of derive_claims
        have hsuc : i.succ = ⟨i.val.succ, Nat.succ_lt_succ i.isLt⟩ := Fin.ext rfl
        simp only [generate_honest_transcript, derive_claims, next_claim, hsuc]
    · -- final_ok: final claim equals polynomial evaluation
      simp only [decide_eq_true_eq]
      -- Use the helper lemma that handles dependent types via induction
      exact honest_transcript_final_eq_eval n p r
  have hfilter :
      (Finset.univ.filter (fun r => AcceptsEvent p (generate_honest_transcript p (true_sum p) r)) : Finset (Fin n → 𝔽))
        = Finset.univ := by
    ext r
    simp [hE r]

  simp [prob_over_challenges, all_assignments_n, hfilter]
