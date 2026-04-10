/-
  BadTranscriptAnalysis.lean

  Lemma showing that acceptance with a bad transcript implies
  there exists a round where the prover's polynomial disagrees
  with the honest polynomial but they agree on the next claim.
-/

import Sumcheck.Properties.Events.Accepts
import Sumcheck.Properties.Events.BadRound
import Sumcheck.Properties.Lemmas.BadTranscript
import Sumcheck.Properties.Lemmas.Accepts
import Sumcheck.Properties.Lemmas.HonestRoundProofs

lemma accepts_and_bad_implies_exists_round_disagree_but_agree
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (st : SumcheckStatement 𝔽 n)
  (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n)))
  (r : Fin n → 𝔽) :
  AcceptsAndBadTranscriptOnChallenges st P r →
    ∃ i : Fin n, RoundDisagreeButAgreeAtChallenge st P r i := by
  classical
  intro h
  rcases h with ⟨hAcc, hBad⟩
  let t : Transcript 𝔽 n := proverTranscript st P r

  -- pick the last bad round
  have hLast : LastBadRound st P r := by
    exact badTranscript_implies_lastBadRound st P r (by simpa [t] using hBad)

  rcases hLast with ⟨i, hi_bad, hi_after⟩
  refine ⟨i, ?_⟩

  have hneq : t.round_polys i ≠ honest_round_poly st.domain (p := st.polynomial) (ch := r) i := by
    simpa [t] using hi_bad

  have hsuc :
      (i.succ : Fin (n + 1)) =
        ⟨i.val.succ, by exact Nat.succ_lt_succ i.isLt⟩ := by
    ext; rfl

  by_cases hlast : i.val.succ = n
  · -- last-round case
    have hfinal : t.claims (Fin.last n) = CPoly.CMvPolynomial.eval t.challenges st.polynomial := by
      exact (decide_eq_true_eq.mp (acceptsEvent_final_ok st.domain (p := st.polynomial) (t := t) hAcc))

    have hlast_idx : (Fin.last n : Fin (n + 1)) = i.succ := by
      ext; simp [Fin.last]; omega

    have hfinal' : t.claims (i.succ) = CPoly.CMvPolynomial.eval t.challenges st.polynomial := by
      simpa [hlast_idx] using hfinal

    have ht_claim_last :
        next_claim (𝔽 := 𝔽) (round_challenge := r i) (t.round_polys i)
          = CPoly.CMvPolynomial.eval r st.polynomial := by
      have := hfinal'.symm
      have htmp :
          CPoly.CMvPolynomial.eval r st.polynomial =
            next_claim (𝔽 := 𝔽) (round_challenge := r i) (t.round_polys i) := by
        simpa [t, proverTranscript, generate_honest_claims, next_claim, hsuc] using this
      simpa [eq_comm] using htmp

    have honest_last :
        next_claim (𝔽 := 𝔽) (round_challenge := r i) (honest_round_poly st.domain (p := st.polynomial) (ch := r) i)
          = CPoly.CMvPolynomial.eval r st.polynomial := by
      simpa using (honest_last_round st.domain (p := st.polynomial) (r := r) (i := i) hlast)

    have hnc :
        next_claim (𝔽 := 𝔽) (round_challenge := r i) (t.round_polys i)
          =
        next_claim (𝔽 := 𝔽) (round_challenge := r i) (honest_round_poly st.domain (p := st.polynomial) (ch := r) i) := by
      calc
        next_claim (𝔽 := 𝔽) (round_challenge := r i) (t.round_polys i)
            = CPoly.CMvPolynomial.eval r st.polynomial := ht_claim_last
        _   = next_claim (𝔽 := 𝔽) (round_challenge := r i)
                (honest_round_poly st.domain (p := st.polynomial) (ch := r) i) := by
              simpa using honest_last.symm

    refine ⟨hneq, ?_⟩
    simpa [next_claim] using hnc

  · -- not-last-round case
    have hlt : i.val.succ < n := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt i.isLt) hlast
    let j : Fin n := ⟨i.val.succ, hlt⟩

    have hj_honest : t.round_polys j = honest_round_poly st.domain (p := st.polynomial) (ch := r) j := by
      have hij : i < j := by
        exact Fin.lt_def.mpr (Nat.lt_succ_self i.val)
      simpa [t, j] using hi_after j hij

    have hsum :
        st.domain.foldl (fun acc a =>
          acc + CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => a)
            (honest_round_poly st.domain (p := st.polynomial) (ch := r) j)) 0
          =
        t.claims (Fin.castSucc j) := by
      exact acceptsEvent_domain_sum_eq_claim_of_honest st.domain
        (p := st.polynomial) (r := r) (t := t) (i := j) (hi := hj_honest) hAcc

    have hcast : (Fin.castSucc j) = i.succ := by
      ext; simp [j]

    have hclaim_i_succ :
        t.claims (i.succ)
          =
        next_claim (𝔽 := 𝔽) (round_challenge := r i) (t.round_polys i) := by
      simp [t, proverTranscript, generate_honest_claims, next_claim, hsuc]

    have hclaim_j :
        t.claims (Fin.castSucc j)
          =
        next_claim (𝔽 := 𝔽) (round_challenge := r i) (t.round_polys i) := by
      simpa [hcast] using hclaim_i_succ

    have honest_step :
        st.domain.foldl (fun acc a =>
          acc + CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => a)
            (honest_round_poly st.domain (p := st.polynomial) (ch := r) j)) 0
          =
        next_claim (𝔽 := 𝔽) (round_challenge := r i) (honest_round_poly st.domain (p := st.polynomial) (ch := r) i) := by
      simpa [j] using (honest_step_round st.domain (p := st.polynomial) (r := r) (i := i) hlt)

    refine ⟨hneq, ?_⟩
    calc
      next_claim (𝔽 := 𝔽) (round_challenge := r i) (t.round_polys i)
          = t.claims (Fin.castSucc j) := by
              simpa using (Eq.symm hclaim_j)
      _ =
          st.domain.foldl (fun acc a =>
            acc + CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => a)
              (honest_round_poly st.domain (p := st.polynomial) (ch := r) j)) 0 := by
              simpa using hsum.symm
      _ = next_claim (𝔽 := 𝔽) (round_challenge := r i)
            (honest_round_poly st.domain (p := st.polynomial) (ch := r) i) := honest_step
