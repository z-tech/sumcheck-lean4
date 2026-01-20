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

lemma Std.ExtTreeMap.foldl_empty
  {α : Type u} {β : Type v} {cmp : α → α → Ordering} {δ : Type w}
  [Std.TransCmp cmp]
  (f : δ → α → β → δ) (init : δ) :
  Std.ExtTreeMap.foldl (cmp := cmp) f init (∅ : Std.ExtTreeMap α β cmp) = init := by
  classical
  have hnil : ((∅ : Std.ExtTreeMap α β cmp).toList) = [] := by
    exact (Std.ExtTreeMap.toList_eq_nil_iff (t := (∅ : Std.ExtTreeMap α β cmp))).2 rfl
  simp [Std.ExtTreeMap.foldl_eq_foldl_toList, hnil]


lemma Std.ExtTreeMap.foldl_singleton_of_toList
  {α : Type u} {β : Type v} {cmp : α → α → Ordering} {δ : Type w}
  [Std.TransCmp cmp]
  (f : δ → α → β → δ) (init : δ) (t : Std.ExtTreeMap α β cmp) (k : α) (v : β)
  (ht : t.toList = [(k, v)]) :
  Std.ExtTreeMap.foldl (cmp := cmp) f init t = f init k v := by
  classical
  simp [Std.ExtTreeMap.foldl_eq_foldl_toList, ht]


lemma Std.ExtTreeMap.foldl_insert_empty
  {α : Type u} {β : Type v} {cmp : α → α → Ordering} {δ : Type w}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
  [DecidableEq α] [DecidableEq β]
  (f : δ → α → β → δ) (init : δ) (k : α) (v : β) :
  Std.ExtTreeMap.foldl (cmp := cmp) f init
      ((∅ : Std.ExtTreeMap α β cmp).insert k v)
    =
  f init k v := by
  classical
  set t : Std.ExtTreeMap α β cmp := (∅ : Std.ExtTreeMap α β cmp).insert k v

  have hknot : k ∉ (∅ : Std.ExtTreeMap α β cmp) := by simp
  have hsize : t.size = 1 := by
    -- size_insert + size_empty
    simpa [t, hknot] using
      (Std.ExtTreeMap.size_insert
        (t := (∅ : Std.ExtTreeMap α β cmp)) (k := k) (v := v))

  have hlen : t.toList.length = 1 := by
    simp [Std.ExtTreeMap.length_toList, hsize]

  rcases (List.length_eq_one_iff.mp hlen) with ⟨a, ha⟩

  have hget : t[k]? = some v := by
    simpa [t] using
      (Std.ExtTreeMap.getElem?_insert_self
        (t := (∅ : Std.ExtTreeMap α β cmp)) (k := k) (v := v))

  have hmem : (k, v) ∈ t.toList := by
    exact (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some (t := t) (k := k) (v := v)).2 hget

  have haKV : a = (k, v) := by
    -- from membership in a singleton list
    have : (k, v) ∈ [a] := by simpa [ha] using hmem
    simpa using (List.mem_singleton.1 this).symm

  -- foldl over a singleton list
  simp [Std.ExtTreeMap.foldl_eq_foldl_toList, t, ha, haKV]

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

lemma sumcheck_Vector_get_replicate
  {α : Type} {n : ℕ} (a : α) (x : Fin n) :
  (Vector.replicate n a).get x = a := by
  cases x with
  | mk k hk =>
    -- unfold WITHOUT simp (avoids the `Vector.replicate.eq_1` simp loop)
    unfold Vector.replicate
    -- now reduce `Vector.get` to `List.get`
    -- `simp` here is safe: there is no `Vector.replicate` left to loop on
    simpa [Vector.get] using (List.get_replicate (l := n) (a := a) ⟨k, by simpa using hk⟩)

lemma sumcheck_CMvMonomial_zero_get
  {n : ℕ} (x : Fin n) :
  (CPoly.CMvMonomial.zero (n := n)).get x = 0 := by
  -- CMvMonomial.zero = Vector.replicate n 0
  simpa [CPoly.CMvMonomial.zero] using (sumcheck_Vector_get_replicate (n := n) (a := (0 : ℕ)) x)

lemma sumcheck_evalMonomial_zero
  {S : Type} {n : ℕ} [CommSemiring S]
  (vs : Fin n → S) :
  CPoly.MonoR.evalMonomial (n := n) (R := S) vs (CPoly.CMvMonomial.zero (n := n)) = (1 : S) := by
  classical
  -- evalMonomial = ∏ i, vs i ^ m.get i ; and m.get i = 0 for the zero monomial.
  simp [CPoly.MonoR.evalMonomial, sumcheck_CMvMonomial_zero_get]

@[simp]
lemma eval₂_Lawful_C
  {R S : Type} {n : ℕ}
  [Semiring R] [CommSemiring S] [DecidableEq S]
  [BEq R] [LawfulBEq R]
  (f : R →+* S) (vs : Fin n → S) (c : R) :
  CPoly.CMvPolynomial.eval₂ (R := R) (S := S) (n := n) f vs
      (CPoly.Lawful.C (n := n) (R := R) c)
    =
  f c := by
  classical
  by_cases hc : c = 0
  · subst hc
    simp [CPoly.CMvPolynomial.eval₂, CPoly.Lawful.C, CPoly.Unlawful.C]
    simpa using
      (Std.ExtTreeMap.foldl_empty
        (α := CPoly.CMvMonomial n) (β := R) (δ := S)
        (cmp := Ord.compare (α := CPoly.CMvMonomial n))
        (f := fun s m a => f a * CPoly.MonoR.evalMonomial vs m + s)
        (init := (0 : S)))
  ·
    simp [CPoly.CMvPolynomial.eval₂, CPoly.Lawful.C, CPoly.Unlawful.C, hc]

    let t :
        Std.ExtTreeMap (CPoly.CMvMonomial n) R (Ord.compare (α := CPoly.CMvMonomial n)) :=
      (∅ : Std.ExtTreeMap (CPoly.CMvMonomial n) R (Ord.compare (α := CPoly.CMvMonomial n))).insert
        (CPoly.CMvMonomial.zero (n := n)) c

    have h :
        Std.ExtTreeMap.foldl (cmp := Ord.compare (α := CPoly.CMvMonomial n))
          (fun s m a => CPoly.MonoR.evalMonomial vs m * f a + s)
          (0 : S) t
        =
        CPoly.MonoR.evalMonomial vs (CPoly.CMvMonomial.zero (n := n)) * f c := by
      simpa [t] using
        (Std.ExtTreeMap.foldl_insert_empty
          (α := CPoly.CMvMonomial n) (β := R) (δ := S)
          (cmp := Ord.compare (α := CPoly.CMvMonomial n))
          (f := fun s m a => CPoly.MonoR.evalMonomial vs m * f a + s)
          (init := (0 : S))
          (k := CPoly.CMvMonomial.zero (n := n))
          (v := c))

    have hcomm :
        (fun s m a => CPoly.MonoR.evalMonomial vs m * f a + s)
          =
        (fun s m a => f a * CPoly.MonoR.evalMonomial vs m + s) := by
      funext s m a
      simp [mul_comm]

    have h' :
        Std.ExtTreeMap.foldl (cmp := Ord.compare (α := CPoly.CMvMonomial n))
          (fun s m a => f a * CPoly.MonoR.evalMonomial vs m + s)
          (0 : S) t
        =
        f c * CPoly.MonoR.evalMonomial vs (CPoly.CMvMonomial.zero (n := n)) := by
      simpa [hcomm, mul_comm] using h

    have hz :
        CPoly.MonoR.evalMonomial (n := n) (R := S) vs (CPoly.CMvMonomial.zero (n := n)) = (1 : S) := by
      simpa using (sumcheck_evalMonomial_zero (n := n) (S := S) vs)

    -- finish
    simpa [t, hz, mul_one] using h'


def RoundDisagreeButAgreeAtChallenge
{𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
(claim : 𝔽) (p : CPoly.CMvPolynomial n 𝔽) (adv : Adversary 𝔽 n)
(r : Fin n → 𝔽) (i : Fin n) : Prop :=
  let t : Transcript 𝔽 n := AdversaryTranscript claim p adv r
  t.round_polys i ≠ honest_round_poly (p := p) (ch := r) i
    ∧ next_claim (𝔽 := 𝔽) (round_challenge := r i) (t.round_polys i)
        = next_claim (𝔽 := 𝔽) (round_challenge := r i) (honest_round_poly (p := p) (ch := r) i)

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
