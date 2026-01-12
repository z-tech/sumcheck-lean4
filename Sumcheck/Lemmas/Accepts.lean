import Sumcheck.Events.Agreement
import Sumcheck.Events.Accepts
import Sumcheck.Events.BadRound
import Sumcheck.Impl.Verifier

import Sumcheck.Events.Accepts
import Sumcheck.Impl.HonestTranscript

set_option maxHeartbeats 10000000

lemma acceptsEvent_rounds_ok
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽)
  (t : Transcript 𝔽 n) :
  AcceptsEvent p t →
    (List.finRange n).all (fun i : Fin n =>
      verifier_check (ind_degree_k p i) (t.claims (Fin.castSucc i)) (t.round_polys i)
      &&
      decide (t.claims i.succ = next_claim (t.challenges i) (t.round_polys i))
    ) = true := by
  intro hAcc
  dsimp [AcceptsEvent] at hAcc
  simp [is_verifier_accepts_transcript] at hAcc
  have h : (by
      -- name these lets the same way `simp` expanded them
      -- but we don't actually need to name them; `simp` already reduced to (rounds_ok && final_ok) = true
      exact True) := by
    trivial
  -- turn (rounds_ok && final_ok) = true into rounds_ok = true ∧ final_ok = true
  have h' : ( (List.finRange n).all (fun i : Fin n =>
      verifier_check (ind_degree_k p i) (t.claims (Fin.castSucc i)) (t.round_polys i)
      &&
      decide (t.claims i.succ = next_claim (t.challenges i) (t.round_polys i))
    ) = true
    ∧
    decide (t.claims (Fin.last n) = CPoly.CMvPolynomial.eval t.challenges p) = true) := by
    simpa [Bool.and_eq_true] using hAcc
  exact h'.1

lemma acceptsEvent_final_ok
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽)
  (t : Transcript 𝔽 n) :
  AcceptsEvent p t →
    decide (t.claims (Fin.last n) = CPoly.CMvPolynomial.eval t.challenges p) = true := by
  intro hAcc
  dsimp [AcceptsEvent] at hAcc
  simp [is_verifier_accepts_transcript] at hAcc
  have h' :
      (List.finRange n).all (fun i : Fin n =>
        verifier_check (ind_degree_k p i) (t.claims (Fin.castSucc i)) (t.round_polys i)
        &&
        decide (t.claims i.succ = next_claim (t.challenges i) (t.round_polys i))
      ) = true
      ∧
      decide (t.claims (Fin.last n) = CPoly.CMvPolynomial.eval t.challenges p) = true := by
    simpa [Bool.and_eq_true] using hAcc
  exact h'.2

lemma verifier_check_eq_true_iff
  {𝔽 : Type _} [CommRing 𝔽] [DecidableEq 𝔽]
  (max_degree : ℕ)
  (round_claim : 𝔽)
  (round_p : CPoly.CMvPolynomial 1 𝔽) :
  verifier_check (𝔽 := 𝔽) max_degree round_claim round_p = true
    ↔
    (CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (0 : 𝔽)) round_p +
     CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (1 : 𝔽)) round_p
      = round_claim)
    ∧
    (CPoly.CMvPolynomial.degreeOf ⟨0, by decide⟩ round_p ≤ max_degree) := by
  simp [verifier_check]

lemma acceptsEvent_round_facts
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽)
  (t : Transcript 𝔽 n)
  (i : Fin n) :
  AcceptsEvent p t →
    verifier_check (ind_degree_k p i) (t.claims (Fin.castSucc i)) (t.round_polys i) = true
    ∧
    t.claims i.succ = next_claim (t.challenges i) (t.round_polys i) := by
  intro hAcc
  have hRounds := acceptsEvent_rounds_ok (p := p) (t := t) hAcc

  have hall :
      ∀ x, x ∈ List.finRange n →
        (verifier_check (ind_degree_k p x) (t.claims (Fin.castSucc x)) (t.round_polys x)
          &&
          decide (t.claims x.succ = next_claim (t.challenges x) (t.round_polys x))) = true := by
    exact List.all_eq_true.mp hRounds

  have hi_mem : i ∈ List.finRange n := by
    simpa using List.mem_finRange i

  have hix := hall i hi_mem

  have hsplit :
      verifier_check (ind_degree_k p i) (t.claims (Fin.castSucc i)) (t.round_polys i) = true
      ∧ decide (t.claims i.succ = next_claim (t.challenges i) (t.round_polys i)) = true := by
    simpa [Bool.and_eq_true] using hix

  refine ⟨hsplit.1, ?_⟩
  exact decide_eq_true_eq.mp hsplit.2


lemma honest_nextClaim_eq_sum_succ
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽)
  (r : Fin n → 𝔽)
  (i : Fin n)
  (h : i.val.succ < n) :
  let j : Fin n := ⟨i.val.succ, h⟩
  next_claim (r i) (honest_round_poly p r i)
    =
    (CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (0 : 𝔽)) (honest_round_poly p r j)
     +
     CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (1 : 𝔽)) (honest_round_poly p r j)) := by
  -- TODO: algebraic “telescoping” fact for the honest prover
  admit





-- lemma accepts_lastBad_implies_agreementNextClaim
--   {𝔽 : Type _} {n : ℕ}
--   [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
--   (claim : 𝔽)
--   (p : CPoly.CMvPolynomial n 𝔽)
--   (adv : Adversary 𝔽 n)
--   (r : Fin n → 𝔽) :
--   AcceptsEvent p (AdversaryTranscript claim p adv r) →
--   LastBadRound claim p adv r →
--   ∃ i : Fin n,
--     (AdversaryTranscript claim p adv r).round_polys i ≠ honest_round_poly p r i
--     ∧ AgreementNextClaimEvent
--         ((AdversaryTranscript claim p adv r).round_polys i)
--         (honest_round_poly p r i)
--         (r i) := by
--   classical
--   intro hAcc hLast
--   rcases hLast with ⟨i, hi_bad, hi_after⟩
--   refine ⟨i, hi_bad, ?_⟩
--   -- unfold agreement-next-claim
--   dsimp [AgreementNextClaimEvent]
--   -- let t be the adversary transcript
--   let t : Transcript 𝔽 n := AdversaryTranscript claim p adv r

--   -- From AcceptsEvent, get the claim-consistency at round i:
--   have hi_cons :
--       t.claims i.succ = next_claim (t.challenges i) (t.round_polys i) := by
--     have h := (acceptsEvent_round (p := p) (t := t) i hAcc).2
--     simpa [t] using h

--   -- Now split: either i is last round, or there is a next round j = i+1
--   by_cases h : i.val.succ < n
--   · -- non-last case: use the next round j
--     let j : Fin n := ⟨i.val.succ, h⟩
--     have hij : i < j := by
--       exact Fin.lt_iff_val_lt_val.mpr (Nat.lt_succ_self _)

--     -- lastBad says j’s polynomial is honest
--     have hj_honest : t.round_polys j = honest_round_poly p r j := by
--       simpa [t] using hi_after j hij

--     -- Accepts at round j gives verifier_check = true
--     have hj_vcheck :
--         verifier_check (t.claims (Fin.castSucc j)) (t.round_polys j) = true := by
--       exact (acceptsEvent_round (p := p) (t := t) j hAcc).1

--     -- Unfold verifier_check to get the round identity equation for j:
--     have hj_identity :
--         (CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (0 : 𝔽)) (t.round_polys j)
--          +
--          CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (1 : 𝔽)) (t.round_polys j))
--         = t.claims (Fin.castSucc j) := by
--       -- `verifier_check` is a `decide (...)`; `= true` turns into the Prop
--       -- This simp usually works:
--       simpa [Impl.Verifier.verifier_check] using hj_vcheck

--     -- Also, by definition of derive_claims, claim at index j is next_claim of round i:
--     -- (since j.val = i.val+1)
--     have hj_is_i_succ : (Fin.castSucc j) = i.succ := by
--       -- both are in Fin (n+1) with value i.val+1
--       ext
--       simp [j]

--     -- Combine: next_claim at i equals the fixed honest-next-round sum
--     have next_claim_eq_sum_succ :
--         next_claim (r i) (t.round_polys i)
--           =
--         (CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (0 : 𝔽)) (honest_round_poly p r j)
--          +
--          CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (1 : 𝔽)) (honest_round_poly p r j)) := by
--       -- rewrite claim_{i+1} using hi_cons; rewrite the RHS using hj_identity + hj_honest + hj_is_i_succ
--       -- (you may need a couple `simp [t, hj_honest, hj_is_i_succ]` steps here)
--       admit

--     -- Finally, use the honest-step lemma to rewrite that sum as next_claim of honest_round_poly at i
--     -- and we are done.
--     have honest_link :
--         next_claim (r i) (honest_round_poly p r i)
--           =
--         (CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (0 : 𝔽)) (honest_round_poly p r j)
--          +
--          CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (1 : 𝔽)) (honest_round_poly p r j)) := by
--       simpa [j] using (honest_step_nextClaim_eq_roundSucc_sum (p := p) (r := r) (i := i) h)

--     -- Put them together
--     exact by
--       -- next_claim (r i) (t.round_polys i) = next_claim (r i) (honest_round_poly p r i)
--       -- by transitivity through the common “sum_succ”
--       have := congrArg id next_claim_eq_sum_succ
--       -- cleaner:
--       calc
--         next_claim (r i) (t.round_polys i)
--             = (CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (0 : 𝔽)) (honest_round_poly p r j)
--                +
--                CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (1 : 𝔽)) (honest_round_poly p r j)) := next_claim_eq_sum_succ
--         _   = next_claim (r i) (honest_round_poly p r i) := by simpa [honest_link]
--   · -- last-round case: use final_ok instead of “next round”
--     -- Here you use:
--     -- 1) AcceptsEvent’s final_ok: t.claims (Fin.last n) = eval r p
--     -- 2) derive_claims for the last claim says t.claims (Fin.last n) = next_claim (r i) (t.round_polys i)
--     -- 3) honest_last_nextClaim_eq_eval to connect honest_round_poly at i to eval r p
--     admit
