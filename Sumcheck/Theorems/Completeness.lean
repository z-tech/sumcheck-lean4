import Sumcheck.Events.Accepts
import Sumcheck.Probability.Challenges

import Sumcheck.Src.HonestTranscript
import Sumcheck.Src.Hypercube
import Sumcheck.Src.Verifier
import Sumcheck.Events.Accepts

import Sumcheck.Lemmas.Accepts
import Sumcheck.Lemmas.Hypercube

import Sumcheck.Lemmas.HonestRoundProofs
import Sumcheck.Lemmas.SoundnessLemmas
import Sumcheck.Theorems.Soundness

lemma honestTranscript_roundPoly_eq_honestRoundPoly
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽) (r : Fin n → 𝔽) (i : Fin n) :
  (generate_honest_transcript (𝔽 := 𝔽) (n := n) p (true_sum p) r).round_polys i
    =
  honest_round_poly (p := p) (ch := r) i := by
  classical

  -- Force the same `==` that `generate_honest_transcript` uses.
  letI : BEq 𝔽 := instBEqOfDecidableEq (α := 𝔽)

  -- Make it lawful using decide.
  letI : LawfulBEq 𝔽 :=
  { rfl := by
      intro a
      simp
    eq_of_beq := by
      intro a b h
      have hdec : decide (a = b) = true := by
        simpa [instBEqOfDecidableEq] using h
      -- Turn `decide (a=b)=true` into `a=b` using the equality lemma
      have : (decide (a = b) = true) = (a = b) := by
        simp
      -- rewrite hdec into a proof of `a=b`
      -- after rewriting, `hdec : a=b`
      have hab : a = b := by
        -- rewrite the type of hdec
        simpa [this] using hdec
      exact hab }

  cases i with
  | mk k hk =>
    simp [generate_honest_transcript, honest_round_poly, honest_prover_message]


-- Helper: For the honest transcript, the round polynomial at 0+1 equals the claim
-- This is the core sum-identity of the Sumcheck protocol
lemma honest_transcript_sum_identity
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽)
  (r : Fin n → 𝔽)
  (i : Fin n) :
  CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ => (0 : 𝔽))
    ((generate_honest_transcript p (true_sum p) r).round_polys i) +
  CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ => (1 : 𝔽))
    ((generate_honest_transcript p (true_sum p) r).round_polys i) =
  (generate_honest_transcript p (true_sum p) r).claims (Fin.castSucc i) := by
  classical
  -- The honest prover polynomial at 0+1 sums to the residual_sum after fixing 0..i-1
  -- which equals the claim at castSucc i by construction

  -- Rewrite round_polys to honest_round_poly
  have hrp : (generate_honest_transcript p (true_sum p) r).round_polys i =
    honest_round_poly p r i := by
    exact honestTranscript_roundPoly_eq_honestRoundPoly p r i
  rw [hrp]

  -- Use induction on i.val
  cases' h : i.val with k
  · -- Case i = 0: claim is true_sum, and honest_poly(0)+honest_poly(1) = sum over hypercube
    -- claim at castSucc 0 = claim at 0 = true_sum p
    have hcast : Fin.castSucc i = ⟨0, Nat.succ_pos n⟩ := by
      ext; simp [h]
    simp only [generate_honest_transcript, derive_claims, hcast]
    -- Now show honest_round_poly at 0+1 = true_sum p

    -- Since i : Fin n, we have n > 0
    have hn_pos : 0 < n := i.pos

    -- Rewrite n as Nat.succ n' where n' = n - 1
    obtain ⟨n', hn'⟩ : ∃ n' : ℕ, n = Nat.succ n' := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn_pos)

    -- Substitute to get n = Nat.succ n'
    subst hn'

    -- i : Fin (Nat.succ n') with i.val = 0, so i = ⟨0, Nat.succ_pos n'⟩
    have hi_eq : i = ⟨0, Nat.succ_pos n'⟩ := by
      ext
      exact h
    subst hi_eq

    -- Apply the lemma directly
    exact honest_round0_endpoints_eq_true_sum p r
  · -- Case i = succ k: use honest_step_round
    -- claim at castSucc i = next_claim of previous round = next_claim (r prev) (poly prev)
    -- where prev = ⟨k, _⟩ and prev.val.succ = k+1 = i.val

    -- Key facts
    have hi_val : i.val = k + 1 := by simp [h]
    have hk_lt : k < n := by omega
    have hk1_lt : k + 1 < n := by omega

    -- The previous round index
    let prev : Fin n := ⟨k, hk_lt⟩

    -- hstep: endpoints of round ⟨k+1, _⟩ sum to next_claim (r prev) (honest_round_poly prev)
    have hstep := honest_step_round (𝔽 := 𝔽) (n := n) (p := p) (r := r) (i := prev) hk1_lt

    -- Simplify RHS: claim at castSucc i
    simp only [generate_honest_transcript, derive_claims]

    -- i has value k+1, and hstep talks about ⟨(prev.val).succ, _⟩ = ⟨k+1, _⟩
    -- Show honest_round_poly i = honest_round_poly ⟨k+1, hk1_lt⟩
    have hi_eq : i = ⟨k + 1, hk1_lt⟩ := Fin.ext hi_val
    subst hi_eq

    -- Now i = ⟨k+1, hk1_lt⟩ which matches hstep's j
    -- Goal: honest_round_poly(0) + honest_round_poly(1) = next_claim (r k) (honest_prover_message ...)
    -- hstep: same LHS = next_claim (r prev) (honest_round_poly prev)

    -- Show RHS match
    simp only [prev, honest_round_poly, honest_prover_message] at hstep ⊢
    exact hstep

-- Helper lemma: final claim of honest transcript equals polynomial evaluation
-- Pattern match on n to handle dependent types
lemma honest_transcript_final_eq_eval
  {𝔽 : Type _}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] :
  ∀ (n : ℕ) (p : CPoly.CMvPolynomial n 𝔽) (r : Fin n → 𝔽),
  (generate_honest_transcript p (true_sum p) r).claims (Fin.last n) =
    CPoly.CMvPolynomial.eval (generate_honest_transcript p (true_sum p) r).challenges p := by
  intro n
  induction n with
  | zero =>
    intro p r
    -- n = 0: Fin.last 0 = ⟨0, _⟩, derive_claims at 0 = true_sum p
    -- challenges = fun i : Fin 0 => elim0
    -- eval challenges p = true_sum p (both are sum over empty hypercube)
    simp [generate_honest_transcript, derive_claims, Fin.last,
          true_sum, residual_sum, sum_over_hypercube_recursive_zero]
  | succ n' ih =>
    intro p r
    -- n = n' + 1: Fin.last (n'+1) = ⟨n'+1, _⟩
    -- derive_claims at ⟨n'+1, _⟩ = next_claim (r n') (poly n')
    -- Use honest_last_round: next_claim (r last) (honest_round_poly last) = eval r p
    simp only [generate_honest_transcript, derive_claims, Fin.last]

    -- The last round index is ⟨n', Nat.lt_succ_self n'⟩
    let iLast : Fin (n' + 1) := ⟨n', Nat.lt_succ_self n'⟩
    have hLast : iLast.val.succ = n' + 1 := by simp [iLast]

    -- Show the round poly is honest_round_poly
    have hrp : honest_prover_message p (challenge_subset r iLast) (Nat.succ_le_of_lt iLast.isLt) =
        honest_round_poly p r iLast := by
      simp [honest_round_poly, honest_prover_message]
    rw [hrp]

    -- Apply honest_last_round
    exact honest_last_round p r iLast hLast

theorem completeness
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽) :
  prob_over_challenges (𝔽 := 𝔽) (n := n)
    (fun r =>
      AcceptsEvent (𝔽 := 𝔽) (n := n) p
        (generate_honest_transcript (𝔽 := 𝔽) (n := n) p (true_sum p) r))
  = 1 := by
  classical
  -- Perfect completeness: the honest transcript is accepted for every challenge tuple.
  -- Since every element satisfies E, the probability is 1.

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
