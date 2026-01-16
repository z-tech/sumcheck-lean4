import Sumcheck.Events.Agreement
import Sumcheck.Events.Accepts
import Sumcheck.Events.BadRound
import Sumcheck.Src.Verifier

import Sumcheck.Events.Accepts
import Sumcheck.Src.HonestTranscript

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
