import Sumcheck.Lemmas.BadTranscript
import Sumcheck.Lemmas.Accepts
import Sumcheck.Lemmas.Agreement
import Sumcheck.Lemmas.Hypercube
import Sumcheck.Lemmas.HonestRoundProofs
import Sumcheck.Lemmas.SoundnessLemmas

theorem soundness {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (claim : 𝔽)
  (claim_p : CPoly.CMvPolynomial n 𝔽)
  (adv : Adversary 𝔽 n) :
     prob_over_challenges (E := AcceptsAndBadTranscriptOnChallenges claim claim_p adv)
      ≤ n * (max_ind_degree claim_p) / field_size (𝔽 := 𝔽) := by
  classical

  -- Keep AcceptsAndBad in the per-round event.
  let E : Fin n → (Fin n → 𝔽) → Prop :=
    fun i r =>
      AcceptsAndBadTranscriptOnChallenges claim claim_p adv r ∧
        RoundDisagreeButAgreeAtChallenge claim claim_p adv r i

  -- Step 1: Accepts∧Bad implies ∃ i, (Accepts∧Bad ∧ RoundDisagreeButAgreeAtChallenge i).
  have hImp :
      ∀ r : (Fin n → 𝔽),
        AcceptsAndBadTranscriptOnChallenges claim claim_p adv r →
          ∃ i : Fin n, E i r := by
    intro r hAB
    rcases
      accepts_and_bad_implies_exists_round_disagree_but_agree
        (claim := claim) (p := claim_p) (adv := adv) (r := r) hAB
      with ⟨i, hi⟩
    exact ⟨i, ⟨hAB, hi⟩⟩

  have hmono :
      prob_over_challenges (𝔽 := 𝔽) (n := n)
          (fun r => AcceptsAndBadTranscriptOnChallenges claim claim_p adv r)
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
      ≤ n * (max_ind_degree claim_p) / field_size (𝔽 := 𝔽) := by
    simpa [E] using
      sum_accepts_and_round_disagree_but_agree_bound
        (claim := claim) (p := claim_p) (adv := adv)

  exact le_trans (le_trans hmono hunion) hround

lemma all_rounds_honest_of_not_bad
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽)
  (t : Transcript 𝔽 n)
  (hNoBad : ¬ BadTranscriptEvent p t) :
  ∀ i : Fin n,
    t.round_polys i = honest_round_poly (p := p) (ch := t.challenges) i := by
  classical
  intro i
  by_contra hneq
  apply hNoBad
  refine ⟨i, ?_⟩
  simpa [BadRound] using hneq

@[simp] lemma AdversaryTranscript_challenges
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (claim : 𝔽) (p : CPoly.CMvPolynomial n 𝔽) (adv : Adversary 𝔽 n) (r : Fin n → 𝔽) :
  (AdversaryTranscript claim p adv r).challenges = r := by
  rfl

@[simp] lemma derive_claims_zero
  {𝔽} {n : ℕ} [CommRing 𝔽] [DecidableEq 𝔽]
  (initial_claim : 𝔽)
  (round_polys : Fin n → CPoly.CMvPolynomial 1 𝔽)
  (challenges : Fin n → 𝔽) :
  derive_claims (n := n) initial_claim round_polys challenges (0 : Fin (n+1))
    = initial_claim := by
  -- `0 : Fin (n+1)` is definitional equal to `⟨0, Nat.succ_pos n⟩`
  -- so this becomes the definitional equation of derive_claims
  rfl

@[simp] lemma derive_claims_adv_zero
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (claim : 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (adv : Adversary 𝔽 n)
  (r : Fin n → 𝔽) :
  derive_claims claim (fun i => adv p claim i (challenge_subset r i)) r (0 : Fin (n+1))
    = claim := by
  simp

@[simp] lemma AdversaryTranscript_claims_at_zero
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (claim : 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (adv : Adversary 𝔽 n)
  (r : Fin n → 𝔽) :
  (AdversaryTranscript claim p adv r).claims ⟨0, Nat.succ_pos n⟩ = claim := by
  -- unfold AdversaryTranscript; claims is derive_claims; then use the helper above
  simp [AdversaryTranscript]


@[simp] lemma AdversaryTranscript_claims_castSucc_zero
  {𝔽 : Type _} {n' : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (claim : 𝔽) (p : CPoly.CMvPolynomial (Nat.succ n') 𝔽)
  (adv : Adversary 𝔽 (Nat.succ n')) (r : Fin (Nat.succ n') → 𝔽) :
  (AdversaryTranscript claim p adv r).claims (Fin.castSucc (⟨0, Nat.succ_pos n'⟩))
    = claim := by
  -- rewrite castSucc-zero to 0, then use derive_claims_zero via AdversaryTranscript
  simp [AdversaryTranscript]

@[simp] lemma Fin.addCases_left_Fin0
  {α : Type _} {m : ℕ}
  (f : Fin 0 → α) (g : Fin m → α) (i : Fin (0 + m)) :
  Fin.addCases f g i = g (Fin.cast (Nat.zero_add m) i) := by
  cases i with
  | mk k hk =>
      -- hk : k < 0 + m
      -- unfold Fin.addCases and simplify the "k < 0" branch away
      simp [Fin.addCases]


@[simp] lemma addCasesFun_left_Fin0
  {α : Type _} {m : ℕ}
  (f : Fin 0 → α) (g : Fin m → α) :
  addCasesFun f g = (fun i : Fin (0 + m) => g (Fin.cast (Nat.zero_add m) i)) := by
  funext i
  -- unfold addCasesFun to Fin.addCases, then use the simp lemma above
  simp [addCasesFun]

@[simp] lemma Fin.cases_Fin1_apply
  {α : Type _} (a : α) (x : Fin 0 → α) (k : Fin 1) :
  Fin.cases a x k = a := by
  cases k using Fin.cases with
  | zero => rfl
  | succ j =>
      exact (j.elim0)


@[simp] lemma funext_Fin0'
  {α : Type _} (f : Fin 0 → α) :
  f = (fun i => (Fin.elim0 i)) := by
  funext i
  exact (Fin.elim0 i)

@[simp] lemma addCasesFun_Fin0_eq_cons
  {α : Type _} {m : ℕ}
  (g : Fin (m + 1) → α) :
  (fun k : Fin (m + 1) =>
      addCasesFun (fun t : Fin 0 => nomatch t)
        (fun t : Fin (m + 1) => g t)
        (Fin.cast (Nat.zero_add (m+1)).symm k))
    =
  g := by
  funext k
  simp [addCasesFun, Fin.addCases]

@[simp] lemma eval₂_const0_eq
  {𝔽 : Type _} [CommRing 𝔽] [DecidableEq 𝔽]
  (q : CPoly.CMvPolynomial 1 𝔽) :
  CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (0 : 𝔽)) q =
    CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ => (0 : 𝔽)) q := by
  rfl

@[simp] lemma eval₂_const1_eq
  {𝔽 : Type _} [CommRing 𝔽] [DecidableEq 𝔽]
  (q : CPoly.CMvPolynomial 1 𝔽) :
  CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (1 : 𝔽)) q =
    CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ => (1 : 𝔽)) q := by
  rfl

lemma eval₂_sum_over_hypercube_recursive
  {𝔽 : Type _} [CommSemiring 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (z : Fin 1 → 𝔽)
  (b0 b1 : 𝔽)
  {m : ℕ}
  (F : (Fin m → 𝔽) → CPoly.CMvPolynomial 1 𝔽) :
  CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) z
      (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := CPoly.CMvPolynomial 1 𝔽)
        b0 b1 (· + ·) (m := m) F)
    =
  sum_over_hypercube_recursive (𝔽 := 𝔽) (β := 𝔽)
    b0 b1 (· + ·) (m := m) (fun x =>
      CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) z (F x)) := by
  classical
  simpa using
    (sum_over_hypercube_recursive_map
      (𝔽 := 𝔽)
      (β := CPoly.CMvPolynomial 1 𝔽)
      (γ := 𝔽)
      (b0 := b0) (b1 := b1)
      (addβ := (· + ·)) (addγ := (· + ·))
      (g := fun q => CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) z q)
      (hg := by
        intro a b
        simp
      )
      (m := m)
      (F := F))

lemma sum_over_hypercube_recursive_succ_cases
  {𝔽 β : Type _}
  (b0 b1 : 𝔽)
  (add : β → β → β)
  {m : ℕ}
  (F : (Fin (Nat.succ m) → 𝔽) → β) :
  sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add (m := Nat.succ m) F
    =
    add
      (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add (m := m)
        (fun x => F (fun k : Fin (Nat.succ m) => Fin.cases b0 x k)))
      (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add (m := m)
        (fun x => F (fun k : Fin (Nat.succ m) => Fin.cases b1 x k))) := by
  -- start from your existing lemma (the Fin.cons form)
  have h :=
    sum_over_hypercube_recursive_succ
      (𝔽 := 𝔽) (β := β) b0 b1 add (m := m) (F := F)

  -- IMPORTANT: use dsimp, not simp/simpa, to avoid turning the statement into True
  dsimp [Fin.cons] at h

  exact h

@[simp] lemma Fin.cons_eq_cases_const
  {α : Type _} {n : ℕ} (a : α) (x : Fin n → α) :
  (fun i : Fin (n + 1) => (Fin.cons (α := fun _ => α) a x i))
    =
  (fun i : Fin (n + 1) => Fin.cases a x i) := by
  rfl

lemma sum_over_hypercube_recursive_congr_add
  {𝔽 β : Type _} [Field 𝔽]
  {m : ℕ} (b0 b1 : 𝔽)
  {add₁ add₂ : β → β → β}
  {F : (Fin m → 𝔽) → β}
  (hadd : add₁ = add₂) :
  sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add₁ (m := m) F
    =
  sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add₂ (m := m) F := by
  subst hadd
  rfl

lemma eval₂_honest_combined_map_round0_eq_cases
  {𝔽 : Type _} {n' : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (r : Fin (Nat.succ n') → 𝔽) (a : 𝔽) (b : Fin n' → 𝔽) :
  (fun j : Fin (Nat.succ n') =>
      CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
        (RingHom.id 𝔽) (fun _ : Fin 1 => a)
        (honest_combined_map (𝔽 := 𝔽) (n := Nat.succ n')
          (⟨0, Nat.succ_pos n'⟩) (challenge_subset r ⟨0, Nat.succ_pos n'⟩) b j))
    =
  (fun j : Fin (Nat.succ n') => Fin.cases a b j) := by
  classical
  have h :=
    eval₂_honest_combined_map_eq_addCasesFun (𝔽 := 𝔽) (n := Nat.succ n')
      r (⟨0, Nat.succ_pos n'⟩) a b
  simpa [honest_num_open_vars, honest_split_eq, addCasesFun_Fin0_eq_cons] using h

lemma honest_round0_endpoints_eq_true_sum
  {𝔽 : Type _} {n' : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (p : CPoly.CMvPolynomial (Nat.succ n') 𝔽)
  (r : Fin (Nat.succ n') → 𝔽) :
  let i0 : Fin (Nat.succ n') := ⟨0, Nat.succ_pos n'⟩
  CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (0 : 𝔽))
      (honest_round_poly (p := p) (ch := r) i0)
    +
    CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (1 : 𝔽))
      (honest_round_poly (p := p) (ch := r) i0)
    =
    true_sum (p := p) := by
  intro i0

  -- For round 0, honest_num_open_vars = n'
  have hopen : honest_num_open_vars (n := Nat.succ n') i0 = n' := by
    simp [honest_num_open_vars, i0]

  -- Use eval₂_honest_round_poly_eq_sum_eval to rewrite both eval₂ calls
  have h0 := eval₂_honest_round_poly_eq_sum_eval (𝔽 := 𝔽) (n := Nat.succ n')
    (p := p) (r := r) (i := i0) (a := (0 : 𝔽))
  have h1 := eval₂_honest_round_poly_eq_sum_eval (𝔽 := 𝔽) (n := Nat.succ n')
    (p := p) (r := r) (i := i0) (a := (1 : 𝔽))

  -- Rewrite both terms in the sum
  rw [h0, h1]

  -- Unfold true_sum to residual_sum form
  simp only [true_sum, residual_sum]

  -- The goal is now:
  -- sum_over_hypercube_recursive ... (F1) + sum_over_hypercube_recursive ... (F2)
  --   = sum_over_hypercube_recursive ... (F')
  -- Where F1, F2 come from h0, h1 and F' from residual_sum

  -- Both sides use sum_over_hypercube_recursive with m = n'
  -- We need to show they're equal via sum_over_hypercube_recursive_succ

  -- The key is that for i0.val = 0:
  -- - honest_num_open_vars i0 = n'
  -- - The addCasesFun has Fin 0 on left (empty)

  -- Show the inner evaluation functions are equal
  have hinner : ∀ (a : 𝔽) (x : Fin n' → 𝔽),
      (fun k => addCasesFun (fun t => r ⟨t.val, Nat.lt_trans t.isLt i0.isLt⟩)
        (fun t => Fin.cases a x t)
        (Fin.cast (honest_split_eq (n := Nat.succ n') i0).symm k))
      = (fun k => addCasesFun (fun t => t.elim0)
        (Fin.cons a x)
        (Fin.cast (by simp : Nat.succ n' = 0 + Nat.succ n') k)) := by
    intro a x
    funext k
    simp only [addCasesFun, Fin.addCases, i0, honest_num_open_vars]
    cases (Fin.cast _ k) using Fin.addCases with
    | left t => exact Fin.elim0 t
    | right t => simp [Fin.cons]

  -- Use sum_over_hypercube_recursive_congr on each sum
  have hsum0 :
      sum_over_hypercube_recursive (𝔽 := 𝔽) (β := 𝔽) 0 1 (· + ·) (m := n')
        (fun x => CPoly.CMvPolynomial.eval
          (fun k => addCasesFun (fun t => r ⟨t.val, Nat.lt_trans t.isLt i0.isLt⟩)
            (fun t => Fin.cases (0 : 𝔽) x t)
            (Fin.cast (honest_split_eq (n := Nat.succ n') i0).symm k)) p)
      = sum_over_hypercube_recursive (𝔽 := 𝔽) (β := 𝔽) 0 1 (· + ·) (m := n')
        (fun x => CPoly.CMvPolynomial.eval
          (fun k => addCasesFun (fun t => t.elim0) (Fin.cons 0 x)
            (Fin.cast (by simp : Nat.succ n' = 0 + Nat.succ n') k)) p) := by
    exact sum_over_hypercube_recursive_congr _ _ _ (fun x => congr_arg (CPoly.CMvPolynomial.eval · p) (hinner 0 x))

  have hsum1 :
      sum_over_hypercube_recursive (𝔽 := 𝔽) (β := 𝔽) 0 1 (· + ·) (m := n')
        (fun x => CPoly.CMvPolynomial.eval
          (fun k => addCasesFun (fun t => r ⟨t.val, Nat.lt_trans t.isLt i0.isLt⟩)
            (fun t => Fin.cases (1 : 𝔽) x t)
            (Fin.cast (honest_split_eq (n := Nat.succ n') i0).symm k)) p)
      = sum_over_hypercube_recursive (𝔽 := 𝔽) (β := 𝔽) 0 1 (· + ·) (m := n')
        (fun x => CPoly.CMvPolynomial.eval
          (fun k => addCasesFun (fun t => t.elim0) (Fin.cons 1 x)
            (Fin.cast (by simp : Nat.succ n' = 0 + Nat.succ n') k)) p) := by
    exact sum_over_hypercube_recursive_congr _ _ _ (fun x => congr_arg (CPoly.CMvPolynomial.eval · p) (hinner 1 x))

  -- Apply the hsum0 and hsum1 lemmas directly
  have hlhs := congr_arg₂ (· + ·) hsum0 hsum1

  -- Apply sum_over_hypercube_recursive_succ in reverse on RHS
  have hrhs := sum_over_hypercube_recursive_succ (𝔽 := 𝔽) (β := 𝔽) 0 1 (· + ·) (m := n')
    (F := fun x => CPoly.CMvPolynomial.eval
      (fun k => addCasesFun (fun t => t.elim0) x (Fin.cast (by simp : Nat.succ n' = 0 + Nat.succ n') k)) p)

  -- Combine: LHS = (from hsum0/hsum1) = (from hrhs) = RHS
  calc _ = _ + _ := by rfl
       _ = _ := hlhs
       _ = _ := hrhs.symm

lemma claim_eq_true_sum_of_accepts_and_all_rounds_honest
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (claim : 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (adv : Adversary 𝔽 n)
  (r : Fin n → 𝔽)
  (hall :
    ∀ i : Fin n,
      (AdversaryTranscript claim p adv r).round_polys i
        = honest_round_poly (p := p) (ch := (AdversaryTranscript claim p adv r).challenges) i)
  (hAcc : AcceptsEvent p (AdversaryTranscript claim p adv r)) :
  claim = true_sum (p := p) := by
  classical
  let t : Transcript 𝔽 n := AdversaryTranscript claim p adv r

  cases n with
  | zero =>
      -- n = 0: rounds_ok is vacuously true; acceptance gives final_ok
      have hacc_bool :
          is_verifier_accepts_transcript (𝔽 := 𝔽) (n := 0) p t = true := by
        simpa [AcceptsEvent, t] using hAcc

      -- Unfold; with n=0, rounds_ok = true, so we just extract final_ok from `true && final_ok`
      have hfinal_ok :
          decide (t.claims (Fin.last 0) = CPoly.CMvPolynomial.eval t.challenges p) = true := by
        -- `simp` knows List.finRange 0 = [], so `.all` is true and rounds_ok simplifies
        -- leaving `true && final_ok = true`
        simpa [is_verifier_accepts_transcript, t] using hacc_bool

      have hEq :
          t.claims (Fin.last 0) = CPoly.CMvPolynomial.eval t.challenges p := by
        exact of_decide_eq_true hfinal_ok

      -- claims at zero is claim
      have hclaim0 : t.claims (Fin.last 0) = claim := by
        -- Fin.last 0 is definitional 0, so your simp lemma works
        simpa [t] using
          (AdversaryTranscript_claims_at_zero (claim := claim) (p := p) (adv := adv) (r := r))

      -- true_sum for n=0 is eval on the empty assignment
      have htrue0 :
          true_sum (p := p) = CPoly.CMvPolynomial.eval (fun i : Fin 0 => i.elim0) p := by
        simp [true_sum, residual_sum, sum_over_hypercube_recursive_zero]

      -- challenges are the empty function
      have hchal0 : t.challenges = (fun i : Fin 0 => i.elim0) := by
        funext i; exact i.elim0

      -- Finish
      calc
        claim = CPoly.CMvPolynomial.eval (fun i : Fin 0 => i.elim0) p := by
          -- from hEq and hclaim0 and hchal0
          have : claim = CPoly.CMvPolynomial.eval t.challenges p := by
            -- rewrite hEq using hclaim0
            have : claim = t.claims (Fin.last 0) := by simpa [hclaim0]
            -- use hEq
            exact this.trans (hEq.trans (by rfl))
          simpa [hchal0] using this
        _ = true_sum (p := p) := by
          simp [htrue0]

  | succ n' =>
      -- only round 0 is needed
      let i0 : Fin (Nat.succ n') := ⟨0, Nat.succ_pos n'⟩

      -- Expand acceptance to get per-round facts at i0
      have hround :
          verifier_check (ind_degree_k p i0) (t.claims i0.castSucc) (t.round_polys i0) = true ∧
          t.claims i0.succ = next_claim (t.challenges i0) (t.round_polys i0) := by
        -- this is your existing lemma used earlier
        simpa [t] using
          acceptsEvent_round_facts (𝔽 := 𝔽) (n := Nat.succ n') (p := p) (t := t) (i := i0) (by
            simpa [t] using hAcc)

      have hcheck :
          verifier_check (ind_degree_k p i0) (t.claims i0.castSucc) (t.round_polys i0) = true :=
        hround.1

      -- Turn verifier_check = true into endpoint sum identity
      have hsum :
          (CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (0 : 𝔽)) (t.round_polys i0)
            +
           CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (1 : 𝔽)) (t.round_polys i0)
            =
           t.claims i0.castSucc)
          ∧
          CPoly.CMvPolynomial.degreeOf ⟨0, by decide⟩ (t.round_polys i0) ≤ ind_degree_k p i0 := by
        -- your iff lemma for verifier_check
        simpa using
          (verifier_check_eq_true_iff (𝔽 := 𝔽)
            (max_degree := ind_degree_k p i0)
            (round_claim := t.claims i0.castSucc)
            (round_p := t.round_polys i0)).1 hcheck

      have hsum0 :
          CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (0 : 𝔽)) (t.round_polys i0)
          +
          CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (1 : 𝔽)) (t.round_polys i0)
          =
          t.claims i0.castSucc :=
        hsum.1

      -- round 0 poly is honest by hall
      have hi0 :
          t.round_polys i0 = honest_round_poly (p := p) (ch := t.challenges) i0 := by
        simpa [t, AdversaryTranscript] using hall i0

      -- claims at castSucc-zero is claim (this fixes your “match i0.castSucc” goal)
      have hclaim0 : t.claims i0.castSucc = claim := by
        simpa [t] using
          (AdversaryTranscript_claims_castSucc_zero
            (claim := claim) (p := p) (adv := adv) (r := r))

      -- endpoints of honest round 0 equal true_sum (you said you had this as htrue already)
      have htrue :
          CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (0 : 𝔽))
              (honest_round_poly (p := p) (ch := t.challenges) i0)
          +
          CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (1 : 𝔽))
              (honest_round_poly (p := p) (ch := t.challenges) i0)
          =
          true_sum (p := p) := by
        -- easiest is to reuse your proven helper if you have it,
        -- otherwise the same proof as before:
        simpa [t, i0] using honest_round0_endpoints_eq_true_sum (p := p) (r := r)

      -- Finish: claim = (endpoint sum of t.round_polys 0) = true_sum
      calc
        claim = t.claims i0.castSucc := by simp [hclaim0]
        _ = CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (0 : 𝔽)) (t.round_polys i0)
            +
            CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (1 : 𝔽)) (t.round_polys i0) := by
              -- rewrite hsum0
              symm; exact hsum0
        _ = CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (0 : 𝔽))
              (honest_round_poly (p := p) (ch := t.challenges) i0)
            +
            CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (1 : 𝔽))
              (honest_round_poly (p := p) (ch := t.challenges) i0) := by
              -- rewrite the round poly using hi0
              simp [hi0]
        _ = true_sum (p := p) := htrue

lemma accepts_on_challenges_dishonest_implies_bad
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (claim : 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (adv : Adversary 𝔽 n)
  (r : Fin n → 𝔽)
  (hDish : claim ≠ true_sum (p := p))
  (hAcc : AcceptsEvent p (AdversaryTranscript claim p adv r)) :
  BadTranscriptEvent p (AdversaryTranscript claim p adv r) := by
  classical

  -- Pin canonical BEq/LawfulBEq locally (so honest_round_poly types line up).
  letI : BEq 𝔽 := instBEqOfDecidableEq
  letI : LawfulBEq 𝔽 := by classical exact (inferInstance)

  let t : Transcript 𝔽 n := AdversaryTranscript claim p adv r

  by_contra hNoBad

  -- from ¬BadTranscriptEvent, all rounds are honest
  have hall :
      ∀ i : Fin n,
        t.round_polys i = honest_round_poly (p := p) (ch := t.challenges) i :=
    all_rounds_honest_of_not_bad (p := p) (t := t) hNoBad

  -- transport to the exact "hall" shape for the bridge lemma (AdversaryTranscript ...).challenges
  have hall' :
      ∀ i : Fin n,
        (AdversaryTranscript claim p adv r).round_polys i
          =
        honest_round_poly (p := p) (ch := (AdversaryTranscript claim p adv r).challenges) i := by
    intro i
    -- t is definitional equal to the adversary transcript
    simpa [t] using hall i

  have hEq : claim = true_sum (p := p) :=
    claim_eq_true_sum_of_accepts_and_all_rounds_honest
      (claim := claim) (p := p) (adv := adv) (r := r)
      (hall := hall') (hAcc := hAcc)

  exact hDish hEq

theorem soundness_dishonest {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (claim : 𝔽)
  (claim_p : CPoly.CMvPolynomial n 𝔽)
  (adv : Adversary 𝔽 n)
  (h : claim ≠ true_sum (p := claim_p)) :
  prob_over_challenges (E := AcceptsOnChallenges claim claim_p adv)
    ≤ n * (max_ind_degree claim_p) / field_size (𝔽 := 𝔽) := by
  classical

  -- Key reduction: dishonest claim ⇒ (accept → bad), hence accept ⊆ (accept ∧ bad).
  have hImp :
      ∀ r : (Fin n → 𝔽),
        AcceptsOnChallenges claim claim_p adv r →
          AcceptsAndBadTranscriptOnChallenges claim claim_p adv r := by
    intro r hAcc
    refine ⟨?hAccEvent, ?hBad⟩
    · -- acceptance part
      -- (this should simp if AcceptsOnChallenges is defined as AcceptsEvent on AdversaryTranscript)
      simpa [AcceptsOnChallenges, AcceptsAndBadTranscriptOnChallenges] using hAcc
    · -- badness part: THIS is the one helper lemma you need
      -- It should say: if the claim is dishonest and the verifier accepts, then some round_poly differs
      -- from the honest one, i.e. BadTranscriptEvent holds.
      exact
        accepts_on_challenges_dishonest_implies_bad
          (claim := claim) (p := claim_p) (adv := adv) (r := r) h hAcc

  have hmono :
      prob_over_challenges (𝔽 := 𝔽) (n := n)
          (fun r => AcceptsOnChallenges claim claim_p adv r)
        ≤
      prob_over_challenges (𝔽 := 𝔽) (n := n)
          (fun r => AcceptsAndBadTranscriptOnChallenges claim claim_p adv r) :=
    prob_over_challenges_mono (𝔽 := 𝔽) (n := n) hImp

  -- Now just reuse your existing soundness theorem.
  have hsound :
      prob_over_challenges (𝔽 := 𝔽) (n := n)
          (fun r => AcceptsAndBadTranscriptOnChallenges claim claim_p adv r)
        ≤ n * (max_ind_degree claim_p) / field_size (𝔽 := 𝔽) :=
    soundness (𝔽 := 𝔽) (n := n) (claim := claim) (claim_p := claim_p) (adv := adv)

  exact le_trans hmono hsound
