/-
  SoundnessLemmas.lean

  Auxiliary lemmas for the soundness proof, including:
  - accepts_and_bad_implies_exists_round_disagree_but_agree
  - degree_eval2Poly_honest_combined_map_le_ind_degree_k
  - honest_round_poly_degree_le_ind_degree_k
  - prob_over_challenges_fiber_le
  - prob_single_round_accepts_and_disagree_le
  - sum_accepts_and_round_disagree_but_agree_bound
-/

import Mathlib.Data.Rat.Init
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Sumcheck.Probability.Challenges
import Sumcheck.Events.Accepts
import Sumcheck.Events.BadRound
import Sumcheck.Src.Verifier
import Sumcheck.Models.AdversaryTranscript
import Sumcheck.Src.CMvPolynomial
import Sumcheck.Counting.Fields
import ExtTreeMapLemmas.ExtTreeMap
import Std.Data.ExtTreeMap
import Std.Data.ExtTreeMap.Lemmas
import Sumcheck.Lemmas.BadTranscript
import Sumcheck.Lemmas.Accepts
import Sumcheck.Lemmas.HonestProver
import Mathlib

import Sumcheck.Src.HonestTranscript
import Sumcheck.Src.Hypercube
import Sumcheck.Lemmas.Hypercube
import Sumcheck.Lemmas.Agreement
import Sumcheck.Lemmas.Degree
import Sumcheck.Lemmas.List
import Sumcheck.Lemmas.Fin
import Sumcheck.Lemmas.CMvPolynomial
import Sumcheck.Lemmas.Eval2
import Sumcheck.Lemmas.Nat
import Sumcheck.Lemmas.HonestRoundProofs
import Sumcheck.Lemmas.BadTranscriptAnalysis


theorem degree_eval2Poly_honest_combined_map_le_ind_degree_k {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
(p : CPoly.CMvPolynomial n 𝔽) (r : Fin n → 𝔽) (i : Fin n)
(b : Fin (honest_num_open_vars (n := n) i) → 𝔽) :
  CPoly.CMvPolynomial.degreeOf (0 : Fin 1)
      (CPoly.eval₂Poly (𝔽 := 𝔽) (n := n) c1
        (honest_combined_map (𝔽 := 𝔽) (n := n) i (challenge_subset r i) b) p)
    ≤ ind_degree_k p i := by
  classical
  -- substitution map used in the evaluation
  let vs : Fin n → CPoly.CMvPolynomial 1 𝔽 :=
    honest_combined_map (𝔽 := 𝔽) (n := n) i (challenge_subset r i) b
  -- shorthand for the target bound
  let d : ℕ := ind_degree_k p i

  -- Every monomial-coefficient pair in `p.1.toList` has exponent at `i` bounded by d.
  have hexp_le :
      ∀ mc : CPoly.CMvMonomial n × 𝔽,
        mc ∈ p.1.toList → extract_exp_var_i mc.1 i ≤ d := by
    intro mc hmc
    -- turn list membership into a lookup equation
    have hget : p.1[mc.1]? = some mc.2 :=
      (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some (t := p.1) (k := mc.1) (v := mc.2)).1 hmc
    -- the coefficient is nonzero because `p` is Lawful
    have hcne : mc.2 ≠ (0 : 𝔽) := by
      intro hc0
      have : p.1[mc.1]? = some (0 : 𝔽) := by simpa [hc0] using hget
      exact (p.2 mc.1) this

    -- corresponding finsupp monomial
    let m' : Fin n →₀ ℕ := CPoly.CMvMonomial.toFinsupp mc.1

    have hcoeffMv :
        MvPolynomial.coeff m' (CPoly.fromCMvPolynomial (R := 𝔽) p) = mc.2 := by
      -- use the `coeff_eq` bridge and compute the coefficient via `hget`
      simpa [m', CPoly.CMvPolynomial.coeff, hget] using
        (CPoly.coeff_eq (n := n) (R := 𝔽) (m := m') p)

    have hsupp : m' ∈ (CPoly.fromCMvPolynomial (R := 𝔽) p).support := by
      exact (MvPolynomial.mem_support_iff).2 (by simpa [hcoeffMv] using hcne)

    have hmon : m' i ≤ MvPolynomial.degreeOf i (CPoly.fromCMvPolynomial (R := 𝔽) p) :=
      MvPolynomial.monomial_le_degreeOf (i := i) (h_m := hsupp)

    have hdegEq :
        MvPolynomial.degreeOf i (CPoly.fromCMvPolynomial (R := 𝔽) p)
          = CPoly.CMvPolynomial.degreeOf i p := by
      have hfun := (CPoly.degreeOf_equiv (p := p) (S := 𝔽))
      simpa using (congrArg (fun f => f i) hfun).symm

    -- unpack the definitions
    simpa [d, ind_degree_k, extract_exp_var_i, m', hdegEq] using hmon

  -- fold step (use `Add.add`/`Mul.mul` to avoid HAdd/HMul ambiguity)
  let step : CPoly.CMvPolynomial 1 𝔽 → (CPoly.CMvMonomial n × 𝔽) → CPoly.CMvPolynomial 1 𝔽 :=
    fun acc mc =>
      Add.add
        (Mul.mul (c1 (𝔽 := 𝔽) mc.2) (subst_monomial (𝔽 := 𝔽) (n := n) vs mc.1))
        acc

  -- Main fold bound: if every element of the list comes from `p.1.toList`, then folding preserves degree ≤ d.
  have hfold_general :
      ∀ l : List (CPoly.CMvMonomial n × 𝔽),
        (∀ mc ∈ l, mc ∈ p.1.toList) →
        ∀ acc : CPoly.CMvPolynomial 1 𝔽,
          CPoly.CMvPolynomial.degreeOf (0 : Fin 1) acc ≤ d →
          CPoly.CMvPolynomial.degreeOf (0 : Fin 1) (List.foldl step acc l) ≤ d := by
    intro l
    induction l with
    | nil =>
        intro _ acc hacc
        simpa [List.foldl] using hacc
    | cons mc l ih =>
        intro hsub acc hacc
        have hmc_mem : mc ∈ p.1.toList := hsub mc (by simp)
        have hexp : extract_exp_var_i mc.1 i ≤ d := hexp_le mc hmc_mem

        have hsubst :
            CPoly.CMvPolynomial.degreeOf (0 : Fin 1)
                (subst_monomial (n := n) (𝔽 := 𝔽) vs mc.1)
              ≤ extract_exp_var_i mc.1 i := by
          simpa [vs] using
            (degree_subst_monomial_honest_combined_le_exp_i
              (𝔽 := 𝔽) (n := n) (r := r) (i := i) (b := b) (m := mc.1))

        have hc1 : CPoly.CMvPolynomial.degreeOf (0 : Fin 1) (c1 (𝔽 := 𝔽) mc.2) = 0 :=
          degreeOf_c1_eq_zero (𝔽 := 𝔽) (c := mc.2)

        have hmul_le :
            CPoly.CMvPolynomial.degreeOf (0 : Fin 1)
                (Mul.mul (c1 (𝔽 := 𝔽) mc.2)
                  (subst_monomial (n := n) (𝔽 := 𝔽) vs mc.1))
              ≤ d := by
          have hmul' :=
            degreeOf_mul_le_univariate (𝔽 := 𝔽)
              (a := c1 (𝔽 := 𝔽) mc.2)
              (b := subst_monomial (n := n) (𝔽 := 𝔽) vs mc.1)

          have hsum :
              CPoly.CMvPolynomial.degreeOf (0 : Fin 1) (c1 (𝔽 := 𝔽) mc.2)
                +
                CPoly.CMvPolynomial.degreeOf (0 : Fin 1)
                  (subst_monomial (n := n) (𝔽 := 𝔽) vs mc.1)
                ≤ extract_exp_var_i mc.1 i := by
            -- rewrite deg(c1) = 0 and reduce to hsubst
            rw [hc1]
            simpa using hsubst

          have hdeg_mul :
              CPoly.CMvPolynomial.degreeOf (0 : Fin 1)
                  (Mul.mul (c1 (𝔽 := 𝔽) mc.2)
                    (subst_monomial (n := n) (𝔽 := 𝔽) vs mc.1))
                ≤ extract_exp_var_i mc.1 i :=
            le_trans hmul' hsum

          exact le_trans hdeg_mul hexp

        have hstep :
            CPoly.CMvPolynomial.degreeOf (0 : Fin 1) (step acc mc) ≤ d := by
          dsimp [step]
          -- `hadd_degreeOf0_le` is the homogeneous-add degree lemma
          exact hadd_degreeOf0_le (𝔽 := 𝔽) (d := d)
            (a := Mul.mul (c1 (𝔽 := 𝔽) mc.2)
              (subst_monomial (n := n) (𝔽 := 𝔽) vs mc.1))
            (b := acc)
            hmul_le hacc

        have hsub_tail : ∀ mc' ∈ l, mc' ∈ p.1.toList := by
          intro mc' hmc'
          exact hsub mc' (by simp [hmc'])

        -- foldl over (mc :: l)
        simpa [List.foldl] using ih hsub_tail (step acc mc) hstep

  -- initial accumulator degree is 0
  have hinit : CPoly.CMvPolynomial.degreeOf (0 : Fin 1) (c1 (𝔽 := 𝔽) (0 : 𝔽)) ≤ d := by
    have h0 : CPoly.CMvPolynomial.degreeOf (0 : Fin 1) (c1 (𝔽 := 𝔽) (0 : 𝔽)) = 0 :=
      degreeOf_c1_eq_zero (𝔽 := 𝔽) (c := (0 : 𝔽))
    -- rewrite to 0 ≤ d
    rw [h0]
    exact Nat.zero_le d

  have hfold :
      CPoly.CMvPolynomial.degreeOf (0 : Fin 1)
          (List.foldl step (c1 (𝔽 := 𝔽) (0 : 𝔽)) p.1.toList)
        ≤ d := by
    have hsub : ∀ mc ∈ p.1.toList, mc ∈ p.1.toList := by
      intro mc hmc
      exact hmc
    simpa using hfold_general p.1.toList hsub (c1 (𝔽 := 𝔽) (0 : 𝔽)) hinit

  have heq :
      CPoly.eval₂Poly (𝔽 := 𝔽) (n := n) c1 vs p
        =
      List.foldl step (c1 (𝔽 := 𝔽) (0 : 𝔽)) p.1.toList := by
    -- the library lemma expands eval₂Poly as this fold; `step` is definitional equal
    simpa [step] using
      (CPoly.eval₂Poly_eq_list_foldl (𝔽 := 𝔽) (n := n) (f := c1) (vs := vs) (p := p))

  -- conclude
  simpa [vs, d, heq] using hfold

theorem honest_round_poly_degree_le_ind_degree_k {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
(p : CPoly.CMvPolynomial n 𝔽) (r : Fin n → 𝔽) (i : Fin n) :
  CPoly.CMvPolynomial.degreeOf (0 : Fin 1)
      (honest_round_poly (p := p) (ch := r) i)
    ≤ ind_degree_k p i := by
  classical
  dsimp [honest_round_poly]
  -- reduce to the general degree lemma for honest_prover_message_at
  refine degree_honest_prover_message_at_le_of_per_b (𝔽 := 𝔽) (n := n)
    (p := p) (i := i) (challenges := challenge_subset r i) (d := ind_degree_k p i) ?_
  intro b
  -- the remaining goal is exactly the provided axiom
  simpa using
    (degree_eval2Poly_honest_combined_map_le_ind_degree_k (𝔽 := 𝔽) (n := n)
      (p := p) (r := r) (i := i) (b := b))

theorem prob_over_challenges_fiber_le {𝔽 : Type _} {n : ℕ} [Fintype 𝔽] [DecidableEq 𝔽]
(i : Fin (n + 1)) (d : ℕ) (E : (Fin (n + 1) → 𝔽) → Prop) [DecidablePred E]
(hfiber : ∀ rRest : (Fin n → 𝔽),
  ((Finset.univ : Finset 𝔽).filter (fun a => E (Fin.insertNth i a rRest))).card ≤ d) :
  prob_over_challenges (𝔽 := 𝔽) (n := n + 1) E ≤ (d : ℚ) / field_size (𝔽 := 𝔽) := by
  classical
  -- unfold the probability definition
  simp [prob_over_challenges, all_assignments_n, field_size]

  -- The `prob_over_challenges` definition uses a classical decidable instance for `E`.
  -- Rewrite it to use the provided `[DecidablePred E]`.
  have hfilter :
      (@Finset.filter (Fin (n + 1) → 𝔽) E (fun a => Classical.propDecidable (E a)) Finset.univ)
        = (Finset.univ.filter E) := by
    simpa using
      (Finset.filter_congr_decidable (s := (Finset.univ : Finset (Fin (n + 1) → 𝔽)))
        (p := E) (h := fun a => Classical.propDecidable (E a)))

  rw [hfilter]

  -- counting argument
  let fiber (rRest : Fin n → 𝔽) : Finset 𝔽 :=
    (Finset.univ : Finset 𝔽).filter (fun a => E (Fin.insertNth i a rRest))

  let S : Finset (Sigma fun _rRest : (Fin n → 𝔽) => 𝔽) :=
    (Finset.univ : Finset (Fin n → 𝔽)).sigma (fun rRest => fiber rRest)

  let g : (Fin (n + 1) → 𝔽) → Sigma fun _rRest : (Fin n → 𝔽) => 𝔽 :=
    fun r => ⟨Fin.removeNth i r, r i⟩

  have hcard_le : (Finset.univ.filter E).card ≤ S.card := by
    have hg_maps : Set.MapsTo g (Finset.univ.filter E : Set (Fin (n + 1) → 𝔽)) (S : Set _) := by
      intro r hr
      have hrE : E r := by
        simpa [Finset.mem_filter] using hr
      have : (g r).2 ∈ fiber (g r).1 := by
        have hrE' : E (Fin.insertNth i (r i) (Fin.removeNth i r)) := by
          simpa [Fin.insertNth_self_removeNth] using hrE
        simpa [g, fiber, hrE']
      have : g r ∈ S := by
        have : (g r).1 ∈ (Finset.univ : Finset (Fin n → 𝔽)) ∧ (g r).2 ∈ fiber (g r).1 := by
          constructor
          · simp
          · exact this
        simpa [S] using this
      exact this

    have hg_inj : (Finset.univ.filter E : Set (Fin (n + 1) → 𝔽)).InjOn g := by
      intro r hr s hs hgs
      have hrest : Fin.removeNth i r = Fin.removeNth i s := by
        simpa [g] using congrArg Sigma.fst hgs
      have ha : r i = s i := by
        simpa [g] using congrArg Sigma.snd hgs
      have hrrec : Fin.insertNth i (r i) (Fin.removeNth i r) = r := by
        simp
      have hsrec : Fin.insertNth i (s i) (Fin.removeNth i s) = s := by
        simp
      calc
        r = Fin.insertNth i (r i) (Fin.removeNth i r) := by simp
        _ = Fin.insertNth i (s i) (Fin.removeNth i s) := by simp [hrest, ha]
        _ = s := by simp [hsrec]

    exact Finset.card_le_card_of_injOn g hg_maps hg_inj

  have hS_card : S.card = ∑ rRest : (Fin n → 𝔽), (fiber rRest).card := by
    classical
    simp [S]

  have hS_le : S.card ≤ d * Fintype.card (Fin n → 𝔽) := by
    classical
    rw [hS_card]
    have hsum : (∑ rRest : (Fin n → 𝔽), (fiber rRest).card) ≤ ∑ _rRest : (Fin n → 𝔽), d := by
      refine Finset.sum_le_sum ?_
      intro rRest hrRest
      simpa [fiber] using (hfiber rRest)
    refine le_trans hsum ?_
    have hconst : (∑ _rRest : (Fin n → 𝔽), d) = Fintype.card (Fin n → 𝔽) * d := by
      simp
    have hconst' : (∑ _rRest : (Fin n → 𝔽), d) = d * Fintype.card (Fin n → 𝔽) := by
      simp [Nat.mul_comm]
    exact le_of_eq hconst'

  have hcardNat : (Finset.univ.filter E).card ≤ d * Fintype.card (Fin n → 𝔽) :=
    le_trans hcard_le hS_le

  have hcardQ : ((Finset.univ.filter E).card : ℚ) ≤ (d : ℚ) * (Fintype.card (Fin n → 𝔽) : ℚ) := by
    exact_mod_cast hcardNat

  have hden_nonneg : (0 : ℚ) ≤ (Fintype.card 𝔽 : ℚ) ^ (n + 1) := by
    have : (0 : ℚ) ≤ (Fintype.card 𝔽 : ℚ) := by
      exact_mod_cast (Nat.zero_le (Fintype.card 𝔽))
    exact pow_nonneg this (n + 1)

  have hdiv : ((Finset.univ.filter E).card : ℚ) / (Fintype.card 𝔽 : ℚ) ^ (n + 1)
      ≤ ((d : ℚ) * (Fintype.card (Fin n → 𝔽) : ℚ)) / (Fintype.card 𝔽 : ℚ) ^ (n + 1) := by
    exact div_le_div_of_nonneg_right hcardQ hden_nonneg

  refine le_trans hdiv ?_
  by_cases h0 : Fintype.card 𝔽 = 0
  · simp [h0]
  ·
    have h0q : (Fintype.card 𝔽 : ℚ) ≠ 0 := by
      exact_mod_cast h0
    have hpow_ne : (Fintype.card 𝔽 : ℚ) ^ n ≠ 0 := pow_ne_zero n h0q

    -- normalize the remaining goal using the cardinality formula for function spaces
    simp [pow_succ, mul_comm]

    -- show equality, hence the desired inequality
    refine le_of_eq ?_
    -- cancel the common factor (Fintype.card 𝔽)^n
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (mul_div_mul_left (a := (d : ℚ)) (b := (Fintype.card 𝔽 : ℚ))
        (c := (Fintype.card 𝔽 : ℚ) ^ n) hpow_ne)

theorem prob_single_round_accepts_and_disagree_le {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
(claim : 𝔽) (p : CPoly.CMvPolynomial n 𝔽) (adv : Adversary 𝔽 n) (i : Fin n) :
  prob_over_challenges (𝔽 := 𝔽) (n := n)
    (fun r =>
      AcceptsAndBadTranscriptOnChallenges claim p adv r ∧
      RoundDisagreeButAgreeAtChallenge (claim := claim) (p := p) (adv := adv) r i)
    ≤ (max_ind_degree p) / field_size (𝔽 := 𝔽) := by
  classical
  cases n with
  | zero =>
      exact (Fin.elim0 i)
  | succ n' =>
      classical
      let E : (Fin (n' + 1) → 𝔽) → Prop := fun r =>
        AcceptsAndBadTranscriptOnChallenges claim p adv r ∧
        RoundDisagreeButAgreeAtChallenge (claim := claim) (p := p) (adv := adv) r i
      letI : DecidablePred E := Classical.decPred _

      have hfiber : ∀ rRest : (Fin n' → 𝔽),
          ((Finset.univ : Finset 𝔽).filter (fun a => E (Fin.insertNth i a rRest))).card ≤
            max_ind_degree p := by
        intro rRest
        classical
        let r0 : Fin (n' + 1) → 𝔽 := Fin.insertNth i (0 : 𝔽) rRest
        let g : CPoly.CMvPolynomial 1 𝔽 := (AdversaryTranscript claim p adv r0).round_polys i
        let h : CPoly.CMvPolynomial 1 𝔽 := honest_round_poly (p := p) (ch := r0) i
        let S : Finset 𝔽 := (Finset.univ : Finset 𝔽).filter (fun a => E (Fin.insertNth i a rRest))

        by_cases hS : S = ∅
        · simp [S, hS]
        ·
          have hSnonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.2 hS
          rcases hSnonempty with ⟨a0, ha0⟩
          have ha0E : E (Fin.insertNth i a0 rRest) := (Finset.mem_filter.1 ha0).2

          have hchal_eq (a : 𝔽) :
              challenge_subset (Fin.insertNth i a rRest) i = challenge_subset r0 i := by
            funext j
            have hjlt : (⟨j.val, Nat.lt_trans j.isLt i.isLt⟩ : Fin (n' + 1)) < i := by
              exact Fin.lt_iff_val_lt_val.mpr j.isLt
            simp [r0, challenge_subset, Fin.insertNth_apply_below hjlt]

          have hg_eq (a : 𝔽) :
              (AdversaryTranscript claim p adv (Fin.insertNth i a rRest)).round_polys i = g := by
            simp [AdversaryTranscript, g, hchal_eq a]

          have hh_eq (a : 𝔽) :
              honest_round_poly (p := p) (ch := Fin.insertNth i a rRest) i = h := by
            unfold honest_round_poly
            have := congrArg
              (fun cs => honest_prover_message_at (p := p) (i := i) (challenges := cs))
              (hchal_eq a)
            simpa [h, r0] using this

          have hgh_ne : g ≠ h := by
            intro hgh
            have hneq0 :
                (AdversaryTranscript claim p adv (Fin.insertNth i a0 rRest)).round_polys i ≠
                  honest_round_poly (p := p) (ch := Fin.insertNth i a0 rRest) i :=
              (ha0E.2).1
            apply hneq0
            simp [hg_eq a0, hh_eq a0, hgh]

          -- degree bound for g from acceptance at a0
          have hgdeg : CPoly.CMvPolynomial.degreeOf (0 : Fin 1) g ≤ max_ind_degree p := by
            have hAcc : AcceptsEvent p (AdversaryTranscript claim p adv (Fin.insertNth i a0 rRest)) :=
              (ha0E.1).1
            have hAcc' : is_verifier_accepts_transcript (𝔽 := 𝔽) (n := n' + 1) p
                (AdversaryTranscript claim p adv (Fin.insertNth i a0 rRest)) = true := by
              simpa [AcceptsEvent] using hAcc
            have hrounds_ok :
                (List.finRange (n' + 1)).all (fun j : Fin (n' + 1) =>
                  verifier_check (ind_degree_k p j)
                    ((AdversaryTranscript claim p adv (Fin.insertNth i a0 rRest)).claims (Fin.castSucc j))
                    ((AdversaryTranscript claim p adv (Fin.insertNth i a0 rRest)).round_polys j)
                  &&
                  decide
                    ((AdversaryTranscript claim p adv (Fin.insertNth i a0 rRest)).claims j.succ =
                      next_claim
                        ((AdversaryTranscript claim p adv (Fin.insertNth i a0 rRest)).challenges j)
                        ((AdversaryTranscript claim p adv (Fin.insertNth i a0 rRest)).round_polys j)))
                = true := by
              have hsplit :
                  (List.finRange (n' + 1)).all (fun j : Fin (n' + 1) =>
                    verifier_check (ind_degree_k p j)
                      ((AdversaryTranscript claim p adv (Fin.insertNth i a0 rRest)).claims (Fin.castSucc j))
                      ((AdversaryTranscript claim p adv (Fin.insertNth i a0 rRest)).round_polys j)
                    &&
                    decide
                      ((AdversaryTranscript claim p adv (Fin.insertNth i a0 rRest)).claims j.succ =
                        next_claim
                          ((AdversaryTranscript claim p adv (Fin.insertNth i a0 rRest)).challenges j)
                          ((AdversaryTranscript claim p adv (Fin.insertNth i a0 rRest)).round_polys j)))
                  = true
                  ∧
                  decide
                      ((AdversaryTranscript claim p adv (Fin.insertNth i a0 rRest)).claims (Fin.last (n' + 1)) =
                        CPoly.CMvPolynomial.eval
                          (AdversaryTranscript claim p adv (Fin.insertNth i a0 rRest)).challenges p)
                    = true := by
                simpa [is_verifier_accepts_transcript, Bool.and_eq_true] using hAcc'
              exact hsplit.1
            have hall := List.all_eq_true.mp hrounds_ok
            have hi_mem : i ∈ List.finRange (n' + 1) := by
              simp [List.mem_finRange i]
            have hi_pair := hall i hi_mem
            have hi_split :
                verifier_check (ind_degree_k p i)
                    ((AdversaryTranscript claim p adv (Fin.insertNth i a0 rRest)).claims (Fin.castSucc i))
                    ((AdversaryTranscript claim p adv (Fin.insertNth i a0 rRest)).round_polys i)
                  = true
                ∧
                decide
                    ((AdversaryTranscript claim p adv (Fin.insertNth i a0 rRest)).claims i.succ =
                      next_claim
                        ((AdversaryTranscript claim p adv (Fin.insertNth i a0 rRest)).challenges i)
                        ((AdversaryTranscript claim p adv (Fin.insertNth i a0 rRest)).round_polys i))
                  = true := by
              simpa [Bool.and_eq_true] using hi_pair
            have hcheck := hi_split.1
            have hdeg_and :
                (decide
                      (CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (0 : 𝔽))
                            ((AdversaryTranscript claim p adv (Fin.insertNth i a0 rRest)).round_polys i) +
                          CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (1 : 𝔽))
                            ((AdversaryTranscript claim p adv (Fin.insertNth i a0 rRest)).round_polys i) =
                        (AdversaryTranscript claim p adv (Fin.insertNth i a0 rRest)).claims (Fin.castSucc i)))
                  &&
                  decide
                      (CPoly.CMvPolynomial.degreeOf (0 : Fin 1)
                            ((AdversaryTranscript claim p adv (Fin.insertNth i a0 rRest)).round_polys i) ≤
                        ind_degree_k p i)
                  = true := by
              simpa [verifier_check] using hcheck
            have hdeg_true :
                decide
                    (CPoly.CMvPolynomial.degreeOf (0 : Fin 1)
                          ((AdversaryTranscript claim p adv (Fin.insertNth i a0 rRest)).round_polys i) ≤
                      ind_degree_k p i)
                  = true := by
              have hsplit :
                  decide
                      (CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (0 : 𝔽))
                            ((AdversaryTranscript claim p adv (Fin.insertNth i a0 rRest)).round_polys i) +
                          CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (1 : 𝔽))
                            ((AdversaryTranscript claim p adv (Fin.insertNth i a0 rRest)).round_polys i) =
                        (AdversaryTranscript claim p adv (Fin.insertNth i a0 rRest)).claims (Fin.castSucc i))
                    = true
                  ∧
                  decide
                      (CPoly.CMvPolynomial.degreeOf (0 : Fin 1)
                            ((AdversaryTranscript claim p adv (Fin.insertNth i a0 rRest)).round_polys i) ≤
                        ind_degree_k p i)
                    = true := by
                simpa [Bool.and_eq_true] using hdeg_and
              exact hsplit.2
            have hdeg' :
                CPoly.CMvPolynomial.degreeOf (0 : Fin 1)
                      ((AdversaryTranscript claim p adv (Fin.insertNth i a0 rRest)).round_polys i)
                  ≤ ind_degree_k p i :=
              decide_eq_true_eq.mp hdeg_true
            have hdeg'' :
                CPoly.CMvPolynomial.degreeOf (0 : Fin 1)
                      ((AdversaryTranscript claim p adv (Fin.insertNth i a0 rRest)).round_polys i)
                  ≤ max_ind_degree p :=
              le_trans hdeg' (ind_degree_k_le_max_ind_degree (p := p) (k := i))
            simpa [hg_eq a0] using hdeg''

          have hhdeg : CPoly.CMvPolynomial.degreeOf (0 : Fin 1) h ≤ max_ind_degree p := by
            have hh' : CPoly.CMvPolynomial.degreeOf (0 : Fin 1) h ≤ ind_degree_k p i := by
              dsimp [h]
              simpa using (honest_round_poly_degree_le_ind_degree_k (p := p) (r := r0) (i := i))
            exact le_trans hh' (ind_degree_k_le_max_ind_degree (p := p) (k := i))

          have hdiffdeg :
              MvPolynomial.degreeOf (⟨0, by decide⟩ : Fin 1) (difference_poly g h)
                ≤ max_ind_degree p := by
            classical
            let i0 : Fin 1 := 0
            have hEqg :
                CPoly.CMvPolynomial.degreeOf i0 g =
                  MvPolynomial.degreeOf (σ := Fin 1) (R := 𝔽) i0 (CPoly.fromCMvPolynomial g) := by
              simpa using congrArg (fun f => f i0) (CPoly.degreeOf_equiv (p := g) (S := 𝔽))
            have hEqh :
                CPoly.CMvPolynomial.degreeOf i0 h =
                  MvPolynomial.degreeOf (σ := Fin 1) (R := 𝔽) i0 (CPoly.fromCMvPolynomial h) := by
              simpa using congrArg (fun f => f i0) (CPoly.degreeOf_equiv (p := h) (S := 𝔽))
            have hgdeg' :
                MvPolynomial.degreeOf (σ := Fin 1) (R := 𝔽) i0 (CPoly.fromCMvPolynomial g)
                  ≤ max_ind_degree p := by
              simpa [i0, hEqg] using hgdeg
            have hhdeg' :
                MvPolynomial.degreeOf (σ := Fin 1) (R := 𝔽) i0 (CPoly.fromCMvPolynomial h)
                  ≤ max_ind_degree p := by
              simpa [i0, hEqh] using hhdeg
            have hsub_le :
                MvPolynomial.degreeOf (σ := Fin 1) (R := 𝔽) i0 (CPoly.fromCMvPolynomial g - CPoly.fromCMvPolynomial h)
                  ≤
                max (MvPolynomial.degreeOf (σ := Fin 1) (R := 𝔽) i0 (CPoly.fromCMvPolynomial g))
                    (MvPolynomial.degreeOf (σ := Fin 1) (R := 𝔽) i0 (CPoly.fromCMvPolynomial h)) :=
              MvPolynomial.degreeOf_sub_le (R := 𝔽) (σ := Fin 1) i0 (CPoly.fromCMvPolynomial g) (CPoly.fromCMvPolynomial h)
            have hmax_le :
                max
                    (MvPolynomial.degreeOf (σ := Fin 1) (R := 𝔽) i0 (CPoly.fromCMvPolynomial g))
                    (MvPolynomial.degreeOf (σ := Fin 1) (R := 𝔽) i0 (CPoly.fromCMvPolynomial h))
                  ≤ max_ind_degree p :=
              max_le_iff.mpr ⟨hgdeg', hhdeg'⟩
            have :
                MvPolynomial.degreeOf (σ := Fin 1) (R := 𝔽) i0 (difference_poly g h)
                  ≤ max_ind_degree p := by
              simpa [difference_poly, i0] using le_trans hsub_le hmax_le
            simpa [i0] using this

          have hagree_card :
              ({a ∈ (Finset.univ : Finset 𝔽) |
                  next_claim (𝔽 := 𝔽) (round_challenge := a) g =
                    next_claim (𝔽 := 𝔽) (round_challenge := a) h}).card
                ≤ max_ind_degree p := by
            let agreeA : Finset 𝔽 :=
              {a ∈ (Finset.univ : Finset 𝔽) |
                next_claim (𝔽 := 𝔽) (round_challenge := a) g =
                  next_claim (𝔽 := 𝔽) (round_challenge := a) h}
            let agreeF : Finset (Fin 1 → 𝔽) :=
              {assignment ∈ (Finset.univ : Finset (Fin 1 → 𝔽)) |
                CPoly.CMvPolynomial.eval assignment g = CPoly.CMvPolynomial.eval assignment h}

            have hmap : agreeA.card ≤ agreeF.card := by
              classical
              have hmaps : Set.MapsTo (fun a : 𝔽 => (fun _ : Fin 1 => a)) (agreeA : Set 𝔽) (agreeF : Set (Fin 1 → 𝔽)) := by
                intro a ha
                have haEq : next_claim (𝔽 := 𝔽) (round_challenge := a) g =
                    next_claim (𝔽 := 𝔽) (round_challenge := a) h := (Finset.mem_filter.1 ha).2
                refine Finset.mem_filter.2 ?_
                constructor
                · simp
                · simpa [agreeF, next_claim] using haEq

              have hinj : Set.InjOn (fun a : 𝔽 => (fun _ : Fin 1 => a)) (agreeA : Set 𝔽) := by
                intro a1 ha1 a2 ha2 hEq
                have : (fun _ : Fin 1 => a1) 0 = (fun _ : Fin 1 => a2) 0 := congrArg (fun f => f 0) hEq
                simpa using this

              exact Finset.card_le_card_of_injOn (s := agreeA) (t := agreeF)
                (f := fun a : 𝔽 => (fun _ : Fin 1 => a)) hmaps hinj

            have hAgreeF : agreeF.card = count_assignments_causing_agreement g h := by
              simp [count_assignments_causing_agreement, agreeF, all_assignments_n, AgreementAtEvent, AgreementEvent,
                -AgreementEvent_eval_equiv]

            have hprob := prob_agreement_le_degree_over_field_size (𝔽 := 𝔽) g h hgh_ne

            have hprob' :
                (count_assignments_causing_agreement g h : ℚ) / (count_all_assignments_n (𝔽 := 𝔽) 1 : ℚ)
                  ≤
                (MvPolynomial.degreeOf (⟨0, by decide⟩ : Fin 1) (difference_poly g h) : ℚ)
                  / (field_size (𝔽 := 𝔽) : ℚ) := by
              -- unfold prob_agreement_at_random_challenge
              simpa [prob_agreement_at_random_challenge] using hprob

            have hdenom : count_all_assignments_n (𝔽 := 𝔽) 1 = field_size (𝔽 := 𝔽) := by
              simp [count_all_assignments_n, field_size, all_assignments_n]

            have hprob'' :
                (count_assignments_causing_agreement g h : ℚ) / (field_size (𝔽 := 𝔽) : ℚ)
                  ≤
                (MvPolynomial.degreeOf (⟨0, by decide⟩ : Fin 1) (difference_poly g h) : ℚ)
                  / (field_size (𝔽 := 𝔽) : ℚ) := by
              simpa [hdenom] using hprob'

            have hpos : 0 < (field_size (𝔽 := 𝔽) : ℚ) := by
              have : 0 < field_size (𝔽 := 𝔽) := by
                simpa [field_size] using (Fintype.card_pos_iff.2 ⟨(0 : 𝔽)⟩)
              exact_mod_cast this

            have hne : (field_size (𝔽 := 𝔽) : ℚ) ≠ 0 := ne_of_gt hpos

            have hcount_le_deg :
                (count_assignments_causing_agreement g h : ℚ)
                  ≤ (MvPolynomial.degreeOf (⟨0, by decide⟩ : Fin 1) (difference_poly g h) : ℚ) := by
              -- multiply both sides by denom
              have := mul_le_mul_of_nonneg_right hprob'' (le_of_lt hpos)
              -- simplify ((a/d)*d) = a
              -- use field_simp
              --
              -- First rewrite divisions as multiplication by inv
              --
              -- simp should close after rewriting
              --
              simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hne] using this

            have hcount_nat :
                count_assignments_causing_agreement g h
                  ≤ MvPolynomial.degreeOf (⟨0, by decide⟩ : Fin 1) (difference_poly g h) := by
              exact_mod_cast hcount_le_deg

            have hagreeF_le : agreeF.card ≤ max_ind_degree p := by
              have : agreeF.card ≤ MvPolynomial.degreeOf (⟨0, by decide⟩ : Fin 1) (difference_poly g h) := by
                simpa [hAgreeF] using hcount_nat
              exact le_trans this hdiffdeg

            have : agreeA.card ≤ max_ind_degree p := le_trans hmap hagreeF_le
            simpa [agreeA] using this

          have hS_le : S.card ≤
              ({a ∈ (Finset.univ : Finset 𝔽) |
                  next_claim (𝔽 := 𝔽) (round_challenge := a) g =
                    next_claim (𝔽 := 𝔽) (round_challenge := a) h}).card := by
            refine Finset.card_le_card ?_
            intro a ha
            have haE : E (Fin.insertNth i a rRest) := (Finset.mem_filter.1 ha).2
            let r : Fin (n' + 1) → 𝔽 := Fin.insertNth i a rRest
            have hEqNext :
                next_claim (𝔽 := 𝔽) (round_challenge := r i)
                    ((AdversaryTranscript claim p adv r).round_polys i)
                  =
                next_claim (𝔽 := 𝔽) (round_challenge := r i)
                    (honest_round_poly (p := p) (ch := r) i) :=
              (haE.2).2
            have hri : r i = a := by
              simp [r]
            have hg' : (AdversaryTranscript claim p adv r).round_polys i = g := by
              simpa [r] using hg_eq a
            have hh' : honest_round_poly (p := p) (ch := r) i = h := by
              simpa [r] using hh_eq a
            refine Finset.mem_filter.2 ?_
            constructor
            · simp
            · simpa [hri, hg', hh'] using hEqNext

          exact le_trans hS_le hagree_card

      simpa [E] using
        (prob_over_challenges_fiber_le (𝔽 := 𝔽) (n := n') (i := i) (d := max_ind_degree p)
          (E := E) (hfiber := hfiber))

theorem sum_accepts_and_round_disagree_but_agree_bound {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
(claim : 𝔽) (p : CPoly.CMvPolynomial n 𝔽) (adv : Adversary 𝔽 n) :
  (∑ i : Fin n,
      prob_over_challenges (𝔽 := 𝔽) (n := n)
        (fun r =>
          AcceptsAndBadTranscriptOnChallenges claim p adv r ∧
          RoundDisagreeButAgreeAtChallenge (claim := claim) (p := p) (adv := adv) r i))
    ≤ n * (max_ind_degree p) / field_size (𝔽 := 𝔽) := by
  classical
  -- Sum the pointwise bounds.
  have hsum :
      (∑ i : Fin n,
          prob_over_challenges (𝔽 := 𝔽) (n := n)
            (fun r =>
              AcceptsAndBadTranscriptOnChallenges claim p adv r ∧
              RoundDisagreeButAgreeAtChallenge (claim := claim) (p := p) (adv := adv) r i))
        ≤ ∑ i : Fin n, ((max_ind_degree p : ℚ) / (field_size (𝔽 := 𝔽) : ℚ)) := by
    -- `Fintype.sum_mono` works in any ordered additive commutative monoid.
    refine Fintype.sum_mono ?_
    intro i
    -- Coerce the Nat ratio to ℚ to avoid Nat division.
    simpa using
      (prob_single_round_accepts_and_disagree_le (𝔽 := 𝔽) (n := n)
        (claim := claim) (p := p) (adv := adv) (i := i))

  -- Evaluate the constant RHS sum and finish.
  calc
    (∑ i : Fin n,
        prob_over_challenges (𝔽 := 𝔽) (n := n)
          (fun r =>
            AcceptsAndBadTranscriptOnChallenges claim p adv r ∧
            RoundDisagreeButAgreeAtChallenge (claim := claim) (p := p) (adv := adv) r i))
        ≤ ∑ i : Fin n, ((max_ind_degree p : ℚ) / (field_size (𝔽 := 𝔽) : ℚ)) := hsum
    _ = (n : ℚ) * ((max_ind_degree p : ℚ) / (field_size (𝔽 := 𝔽) : ℚ)) := by
      -- sum of a constant over `Fin n`
      simp
    _ = n * (max_ind_degree p) / field_size (𝔽 := 𝔽) := by
      -- put it back in the form used by the statement
      simp [div_eq_mul_inv, mul_left_comm, mul_comm]
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

@[simp] lemma Fin.cons_eq_cases_const
  {α : Type _} {n : ℕ} (a : α) (x : Fin n → α) :
  (fun i : Fin (n + 1) => (Fin.cons (α := fun _ => α) a x i))
    =
  (fun i : Fin (n + 1) => Fin.cases a x i) := by
  rfl

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
