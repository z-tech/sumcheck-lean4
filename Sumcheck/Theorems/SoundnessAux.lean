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

open scoped BigOperators

lemma prob_over_challenges_mono
  {𝔽 : Type _} {n : ℕ} [Fintype 𝔽]
  {E F : (Fin n → 𝔽) → Prop}
  (h : ∀ r, E r → F r) :
  prob_over_challenges (𝔽 := 𝔽) (n := n) E ≤ prob_over_challenges (𝔽 := 𝔽) (n := n) F := by
  classical
  let Ω : Finset (Fin n → 𝔽) := all_assignments_n (𝔽 := 𝔽) n
  have hsub : Ω.filter E ⊆ Ω.filter F := by
    intro r hr
    have hrΩ : r ∈ Ω := (Finset.mem_filter.1 hr).1
    have hE : E r := (Finset.mem_filter.1 hr).2
    exact Finset.mem_filter.2 ⟨hrΩ, h r hE⟩
  have hcard : ((Ω.filter E).card : ℚ) ≤ ((Ω.filter F).card : ℚ) := by
    exact_mod_cast (Finset.card_le_card hsub)
  have hΩnonneg : (0 : ℚ) ≤ (Ω.card : ℚ) := by
    exact_mod_cast (Nat.zero_le Ω.card)
  have hdiv := div_le_div_of_nonneg_right hcard hΩnonneg
  simpa [prob_over_challenges, Ω] using hdiv


lemma prob_over_challenges_exists_le_sum
  {𝔽 : Type _} {n : ℕ} [Fintype 𝔽]
  (E : Fin n → (Fin n → 𝔽) → Prop) :
  prob_over_challenges (𝔽 := 𝔽) (n := n) (fun r => ∃ i : Fin n, E i r)
    ≤
  ∑ i : Fin n, prob_over_challenges (𝔽 := 𝔽) (n := n) (fun r => E i r) := by
  classical

  letI : DecidablePred (fun r : (Fin n → 𝔽) => ∃ i : Fin n, E i r) :=
    Classical.decPred _
  letI (i : Fin n) : DecidablePred (fun r : (Fin n → 𝔽) => E i r) :=
    Classical.decPred _

  let Ω : Finset (Fin n → 𝔽) := all_assignments_n (𝔽 := 𝔽) n

  have hsubset :
      Ω.filter (fun r => ∃ i : Fin n, E i r)
        ⊆
      (Finset.univ : Finset (Fin n)).biUnion (fun i => Ω.filter (fun r => E i r)) := by
    intro r hr
    have hrΩ : r ∈ Ω := (Finset.mem_filter.1 hr).1
    rcases (Finset.mem_filter.1 hr).2 with ⟨i, hi⟩
    refine Finset.mem_biUnion.2 ?_
    refine ⟨i, by simp, ?_⟩
    exact Finset.mem_filter.2 ⟨hrΩ, hi⟩

  have h1_nat :
      (Ω.filter (fun r => ∃ i : Fin n, E i r)).card
        ≤
      ((Finset.univ : Finset (Fin n)).biUnion (fun i => Ω.filter (fun r => E i r))).card := by
    exact Finset.card_le_card hsubset

  have h2_nat :
      ((Finset.univ : Finset (Fin n)).biUnion (fun i => Ω.filter (fun r => E i r))).card
        ≤
      ∑ i : Fin n, (Ω.filter (fun r => E i r)).card := by
    simpa using
      (Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin n)))
        (t := fun i => Ω.filter (fun r => E i r)))

  have hcard :
      ((Ω.filter (fun r => ∃ i : Fin n, E i r)).card : ℚ)
        ≤
      ∑ i : Fin n, ((Ω.filter (fun r => E i r)).card : ℚ) := by
    have h1 :
        ((Ω.filter (fun r => ∃ i : Fin n, E i r)).card : ℚ)
          ≤
        (((Finset.univ : Finset (Fin n)).biUnion (fun i => Ω.filter (fun r => E i r))).card : ℚ) := by
      exact_mod_cast h1_nat
    have h2 :
        (((Finset.univ : Finset (Fin n)).biUnion (fun i => Ω.filter (fun r => E i r))).card : ℚ)
          ≤
        ∑ i : Fin n, ((Ω.filter (fun r => E i r)).card : ℚ) := by
      exact_mod_cast h2_nat
    exact le_trans h1 h2

  have hΩnonneg : (0 : ℚ) ≤ (Ω.card : ℚ) := by
    exact_mod_cast (Nat.zero_le Ω.card)

  have hdiv :
      ((Ω.filter (fun r => ∃ i : Fin n, E i r)).card : ℚ) / (Ω.card : ℚ)
        ≤
      (∑ i : Fin n, ((Ω.filter (fun r => E i r)).card : ℚ)) / (Ω.card : ℚ) := by
    exact div_le_div_of_nonneg_right hcard hΩnonneg

  have hsum :
      (∑ i : Fin n, ((Ω.filter (fun r => E i r)).card : ℚ)) / (Ω.card : ℚ)
        =
      ∑ i : Fin n, ((Ω.filter (fun r => E i r)).card : ℚ) / (Ω.card : ℚ) := by
    simp [div_eq_mul_inv, Finset.sum_mul]

  have hfinal :
      ((Ω.filter (fun r => ∃ i : Fin n, E i r)).card : ℚ) / (Ω.card : ℚ)
        ≤
      ∑ i : Fin n, ((Ω.filter (fun r => E i r)).card : ℚ) / (Ω.card : ℚ) := by
    calc
      ((Ω.filter (fun r => ∃ i : Fin n, E i r)).card : ℚ) / (Ω.card : ℚ)
          ≤
        (∑ i : Fin n, ((Ω.filter (fun r => E i r)).card : ℚ)) / (Ω.card : ℚ) := hdiv
      _ = ∑ i : Fin n, ((Ω.filter (fun r => E i r)).card : ℚ) / (Ω.card : ℚ) := hsum
  simpa [prob_over_challenges, Ω] using hfinal

def RoundDisagreeButAgreeAtChallenge
{𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
(claim : 𝔽) (p : CPoly.CMvPolynomial n 𝔽) (adv : Adversary 𝔽 n)
(r : Fin n → 𝔽) (i : Fin n) : Prop :=
  let t : Transcript 𝔽 n := AdversaryTranscript claim p adv r
  t.round_polys i ≠ honest_round_poly (p := p) (ch := r) i
    ∧ next_claim (𝔽 := 𝔽) (round_challenge := r i) (t.round_polys i)
        = next_claim (𝔽 := 𝔽) (round_challenge := r i) (honest_round_poly (p := p) (ch := r) i)

lemma roundDisagreeButAgreeAtChallenge_iff_claims
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (claim : 𝔽) (p : CPoly.CMvPolynomial n 𝔽) (adv : Adversary 𝔽 n)
  (r : Fin n → 𝔽) (i : Fin n) :
  RoundDisagreeButAgreeAtChallenge (claim := claim) (p := p) (adv := adv) r i
    ↔
    let t : Transcript 𝔽 n := AdversaryTranscript claim p adv r
    t.round_polys i ≠ honest_round_poly (p := p) (ch := r) i
      ∧
    t.claims i.succ =
      next_claim (𝔽 := 𝔽) (round_challenge := r i) (honest_round_poly (p := p) (ch := r) i) := by
  classical
  -- unfold the definition
  simp [RoundDisagreeButAgreeAtChallenge]
  -- now unfold how `AdversaryTranscript` defines `claims`
  -- so that `t.claims i.succ` becomes `next_claim (r i) (t.round_polys i)`
  -- (this is just the `derive_claims` recursion step)
  cases i with
  | mk k hk =>
    -- After `cases`, `i.succ` is definitional, and `simp` can reduce `derive_claims`.
    simp [AdversaryTranscript, derive_claims]

-- Core combinatorial extraction lemma from the standard sumcheck soundness proof.
lemma accepts_and_bad_implies_exists_round_disagree_but_agree
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (claim : 𝔽) (p : CPoly.CMvPolynomial n 𝔽) (adv : Adversary 𝔽 n)
  (hfalse : claim ≠ true_sum (𝔽 := 𝔽) p)
  (r : Fin n → 𝔽) :
  AcceptsAndBadOnChallenges claim p adv r →
    ∃ i : Fin n, RoundDisagreeButAgreeAtChallenge (claim := claim) (p := p) (adv := adv) r i := by
  -- TODO: prove this using the standard sumcheck soundness argument:
  -- from accept + incorrect initial claim, extract a round where the prover's polynomial
  -- differs from the honest one but agrees at the verifier challenge.
  sorry

lemma sum_accepts_and_round_disagree_but_agree_bound
{𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
(claim : 𝔽) (p : CPoly.CMvPolynomial n 𝔽) (adv : Adversary 𝔽 n)
 :
  (∑ i : Fin n,
      prob_over_challenges (𝔽 := 𝔽) (n := n)
        (fun r =>
          AcceptsAndBadOnChallenges claim p adv r ∧
          RoundDisagreeButAgreeAtChallenge (claim := claim) (p := p) (adv := adv) r i))
    ≤ n * (max_ind_degree p) / count_field_size (𝔽 := 𝔽) := by
  -- TODO: prove by bounding each round's event probability (Schwartz–Zippel style)
  -- and summing over i.
  sorry
