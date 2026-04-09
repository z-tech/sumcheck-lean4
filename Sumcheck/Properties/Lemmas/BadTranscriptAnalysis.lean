/-
  BadTranscriptAnalysis.lean

  Lemma showing that acceptance with a bad transcript implies
  there exists a round where the adversary polynomial disagrees
  with the honest polynomial but they agree on the next claim.
-/

import Sumcheck.Properties.Events.Accepts
import Sumcheck.Properties.Events.BadRound
import Sumcheck.Properties.Models.AdversaryTranscript
import Sumcheck.Properties.Lemmas.BadTranscript
import Sumcheck.Properties.Lemmas.Accepts
import Sumcheck.Properties.Lemmas.HonestRoundProofs

lemma accepts_and_bad_implies_exists_round_disagree_but_agree
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (domain : List 𝔽)
  (claim : 𝔽) (p : CPoly.CMvPolynomial n 𝔽) (adv : Adversary 𝔽 n)
  (r : Fin n → 𝔽) :
  AcceptsAndBadTranscriptOnChallenges domain claim p adv r →
    ∃ i : Fin n, RoundDisagreeButAgreeAtChallenge domain (claim := claim) (p := p) (adv := adv) r i := by
  classical
  intro h
  rcases h with ⟨hAcc, hBad⟩
  let t : Transcript 𝔽 n := AdversaryTranscript claim p adv r

  -- pick the last bad round
  have hLast : LastBadRound domain (claim := claim) (p := p) (adv := adv) (r := r) := by
    exact badTranscript_implies_lastBadRound domain (claim := claim) (p := p) (adv := adv) (r := r) (by
      simpa [t] using hBad)

  rcases hLast with ⟨i, hi_bad, hi_after⟩
  refine ⟨i, ?_⟩

  have hneq : t.round_polys i ≠ honest_round_poly domain (p := p) (ch := r) i := by
    simpa [t] using hi_bad

  -- A helper that forces `simp`/`match` on `i.succ` to take the `succ`-branch, without `↑i` coercion issues.
  have hsuc :
      (i.succ : Fin (n + 1)) =
        ⟨i.val.succ, by
          -- i.val.succ < n+1
          exact Nat.succ_lt_succ i.isLt⟩ := by
    ext
    rfl

  -- Split on whether i is the last round (use i.val.succ, not (↑i).succ, to avoid coercion ambiguity).
  by_cases hlast : i.val.succ = n
  · -- last-round case
    -- If you ever need the coerced versions, derive them explicitly:
    have hlast_coe : i.val.succ = n := hlast

    have hlast_add : n = i.val + 1 := by
      simpa [Nat.succ_eq_add_one] using hlast.symm
    have hfinal : t.claims (Fin.last n) = CPoly.CMvPolynomial.eval t.challenges p := by
      have hdec := acceptsEvent_final_ok domain (p := p) (t := t) hAcc
      exact (decide_eq_true_eq.mp hdec)

    -- relate Fin.last n to i.succ using hlast
    have hlast_idx : (Fin.last n : Fin (n + 1)) = i.succ := by
      ext
      -- val(Fin.last n)=n, val(i.succ)=i.val.succ; use hlast
      simpa [Fin.last, hlast]

    have hfinal' : t.claims (i.succ) = CPoly.CMvPolynomial.eval t.challenges p := by
      simpa [hlast_idx] using hfinal

    -- from hfinal' and definitional expansions, get next_claim (bad poly) = eval r p
    have ht_claim_last :
        next_claim (𝔽 := 𝔽) (round_challenge := r i) (t.round_polys i)
          = CPoly.CMvPolynomial.eval r p := by
      have := hfinal'.symm
      have htmp :
          CPoly.CMvPolynomial.eval r p =
            next_claim (𝔽 := 𝔽) (round_challenge := r i) (t.round_polys i) := by
        simpa [t, AdversaryTranscript, generate_honest_claims, next_claim, hsuc] using this
      simpa [eq_comm] using htmp

    have honest_last :
        next_claim (𝔽 := 𝔽) (round_challenge := r i) (honest_round_poly domain (p := p) (ch := r) i)
          = CPoly.CMvPolynomial.eval r p := by
      simpa using (honest_last_round domain (p := p) (r := r) (i := i) hlast)

    -- Turn equality of next_claim into equality of eval₂.
    have hnc :
        next_claim (𝔽 := 𝔽) (round_challenge := r i) (t.round_polys i)
          =
        next_claim (𝔽 := 𝔽) (round_challenge := r i) (honest_round_poly domain (p := p) (ch := r) i) := by
      calc
        next_claim (𝔽 := 𝔽) (round_challenge := r i) (t.round_polys i)
            = CPoly.CMvPolynomial.eval r p := ht_claim_last
        _   = next_claim (𝔽 := 𝔽) (round_challenge := r i)
                (honest_round_poly domain (p := p) (ch := r) i) := by
              simpa using honest_last.symm

    refine ⟨hneq, ?_⟩
    simpa [next_claim] using hnc

  · -- not-last-round case
    have hlt : i.val.succ < n := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt i.isLt) hlast
    let j : Fin n := ⟨i.val.succ, hlt⟩

    have hj_honest : t.round_polys j = honest_round_poly domain (p := p) (ch := r) j := by
      have hij : i < j := by
        -- j.val = i.val.succ
        exact Fin.lt_iff_val_lt_val.mpr (Nat.lt_succ_self i.val)
      simpa [t, j] using hi_after j hij

    have hsum :
        domain.foldl (fun acc a =>
          acc + CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => a)
            (honest_round_poly domain (p := p) (ch := r) j)) 0
          =
        t.claims (Fin.castSucc j) := by
      exact acceptsEvent_domain_sum_eq_claim_of_honest domain
        (p := p) (r := r) (t := t) (i := j) (hi := hj_honest) hAcc

    -- castSucc j equals i.succ (both have value i.val.succ)
    have hcast : (Fin.castSucc j) = i.succ := by
      ext
      simp [j]

    -- unfold claims at i.succ to get it is next_claim of the previous round polynomial
    have hclaim_i_succ :
        t.claims (i.succ)
          =
        next_claim (𝔽 := 𝔽) (round_challenge := r i) (t.round_polys i) := by
      simp [t, AdversaryTranscript, generate_honest_claims, next_claim, hsuc]

    have hclaim_j :
        t.claims (Fin.castSucc j)
          =
        next_claim (𝔽 := 𝔽) (round_challenge := r i) (t.round_polys i) := by
      simpa [hcast] using hclaim_i_succ

    -- honest step consistency:
    have honest_step :
        domain.foldl (fun acc a =>
          acc + CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => a)
            (honest_round_poly domain (p := p) (ch := r) j)) 0
          =
        next_claim (𝔽 := 𝔽) (round_challenge := r i) (honest_round_poly domain (p := p) (ch := r) i) := by
      -- `honest_step_round` introduces `j` via a `let`, so we `simpa [j]` to match your `j`.
      simpa [j] using (honest_step_round domain (p := p) (r := r) (i := i) hlt)

    refine ⟨hneq, ?_⟩
    calc
      next_claim (𝔽 := 𝔽) (round_challenge := r i) (t.round_polys i)
          = t.claims (Fin.castSucc j) := by
              -- from hclaim_j : claims = next_claim, flip it
              simpa using (Eq.symm hclaim_j)
      _ =
          domain.foldl (fun acc a =>
            acc + CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => a)
              (honest_round_poly domain (p := p) (ch := r) j)) 0 := by
              simpa using hsum.symm
      _ = next_claim (𝔽 := 𝔽) (round_challenge := r i)
            (honest_round_poly domain (p := p) (ch := r) i) := honest_step
