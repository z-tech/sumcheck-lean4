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
import Sumcheck.Lemmas.Challenges
import Sumcheck.Lemmas.Eval2

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
  simp [RoundDisagreeButAgreeAtChallenge]
  cases i with
  | mk k hk =>
    simp [AdversaryTranscript, derive_claims]

lemma CMvPolynomial.eval_eq_eval₂
  {𝔽 : Type} [CommSemiring 𝔽]
  {n : ℕ}
  (p : CPoly.CMvPolynomial n 𝔽)
  (r : Fin n → 𝔽) :
  CPoly.CMvPolynomial.eval r p
    =
  CPoly.CMvPolynomial.eval₂ (R := 𝔽) (S := 𝔽) (n := n)
    (RingHom.id 𝔽) r p := by
  rfl

lemma two_add (m : ℕ) : 2 + m = 1 + (1 + m) := by
  induction m with
  | zero =>
      rfl
  | succ m ih =>
      change Nat.succ (2 + m) = Nat.succ (1 + (1 + m))
      exact congrArg Nat.succ ih

lemma nat_sub_add_two (n k : ℕ) (hk : k.succ < n) :
    n - (k + 1) = 1 + (n - (k + 2)) := by
  have hle1 : k + 1 ≤ n := Nat.le_of_lt hk
  have hle2 : k + 2 ≤ n := Nat.succ_le_of_lt hk

  -- Let m = n - (k+2), so (k+2) + m = n
  set m : ℕ := n - (k + 2) with hm
  have hsub1 : (k + 1) + (n - (k + 1)) = n := Nat.add_sub_of_le hle1
  have hsub2 : (k + 2) + m = n := by
    simpa [m] using (Nat.add_sub_of_le hle2)

  have heq :
      (k + 1) + (n - (k + 1)) = (k + 1) + (1 + m) := by
    calc
      (k + 1) + (n - (k + 1)) = n := hsub1
      _ = (k + 2) + m := by simpa using hsub2.symm
      _ = (k + 1) + (1 + m) := by
        -- Prove (k+2)+m = (k+1)+(1+m) by reassociating to `k + (2+m)`
        -- then rewriting `2+m` using `two_add`, then reassociating back.
        calc
          (k + 2) + m = k + (2 + m) := by
            -- (k+2)+m = k+(2+m)
            simp [Nat.add_assoc]
          _ = k + (1 + (1 + m)) := by
            -- rewrite the inner 2+m
            rw [two_add m]
          _ = (k + 1) + (1 + m) := by
            -- k + (1 + (1+m)) = (k+1) + (1+m)
            simp [Nat.add_assoc]

  have : n - (k + 1) = 1 + m := Nat.add_left_cancel heq
  simpa [m] using this

lemma honest_num_open_vars_succ {n : ℕ} (i : Fin n) (hlt : i.val.succ < n) :
    honest_num_open_vars (n := n) i
      = honest_num_open_vars (n := n) (⟨i.val.succ, hlt⟩ : Fin n) + 1 := by
  -- unfold to Nat subtraction
  -- honest_num_open_vars k = n - (k.val + 1)
  -- and j.val = i.val+1, so j.val+1 = i.val+2
  have hNat : n - (i.val + 1) = 1 + (n - (i.val + 2)) := by
    simpa using nat_sub_add_two n i.val hlt
  -- put it back in the project’s definition shape
  -- note: `simp` should rewrite the j-val arithmetic
  simpa [honest_num_open_vars, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hNat

lemma List.foldl_mul_pull_out
  {α β : Type _} [Monoid α]
  (h : β → α) :
  ∀ (a : α) (l : List β),
    List.foldl (fun acc x => acc * h x) a l
      =
    a * List.foldl (fun acc x => acc * h x) 1 l
  | a, [] =>
      by
        -- LHS = a, RHS = a * 1
        simpa using (Eq.symm (mul_one a))
  | a, x :: xs =>
      by
        -- recursive instances (IMPORTANT: pass h := h)
        have ih_a :
            List.foldl (fun acc t => acc * h t) (a * h x) xs
              =
            (a * h x) * List.foldl (fun acc t => acc * h t) 1 xs :=
          (List.foldl_mul_pull_out (h := h) (a := a * h x) (l := xs))

        have ih_hx :
            List.foldl (fun acc t => acc * h t) (h x) xs
              =
            (h x) * List.foldl (fun acc t => acc * h t) 1 xs :=
          (List.foldl_mul_pull_out (h := h) (a := h x) (l := xs))

        -- main calc
        calc
          List.foldl (fun acc t => acc * h t) a (x :: xs)
              = List.foldl (fun acc t => acc * h t) (a * h x) xs := rfl
          _ = (a * h x) * List.foldl (fun acc t => acc * h t) 1 xs := ih_a
          _ = a * (h x * List.foldl (fun acc t => acc * h t) 1 xs) := by
                -- reassociate: (a*h x)*rest = a*(h x*rest)
                simp [mul_assoc]
          _ = a * List.foldl (fun acc t => acc * h t) (h x) xs := by
                -- use ih_hx backwards inside `a * _`
                simpa using congrArg (fun z => a * z) ih_hx.symm
          _ = a * List.foldl (fun acc t => acc * h t) (1 * h x) xs := by
                simp
          _ = a * List.foldl (fun acc t => acc * h t) 1 (x :: xs) := rfl

lemma foldl_finRange_mul_eq_prod
  {α : Type _} : ∀ {n : ℕ} [CommMonoid α] (g : Fin n → α),
    List.foldl (fun acc i => acc * g i) 1 (List.finRange n)
      = (∏ i : Fin n, g i)
  | 0, _, g => by
      simp
  | (n+1), inst, g => by
      classical
      -- expand finRange (n+1) and the ∏ over Fin (n+1)
      -- after this simp, the goal becomes the “head * tail” shape
      simp [List.finRange_succ]

      -- rewrite foldl over the mapped list using the existing List.foldl_map
      have hmap :
          List.foldl (fun acc j => acc * g j) (g 0) (List.map Fin.succ (List.finRange n))
            =
          List.foldl (fun acc i => acc * g i.succ) (g 0) (List.finRange n) := by
        simpa using
          (List.foldl_map (f := Fin.succ)
            (g := fun acc (j : Fin (n + 1)) => acc * g j)
            (l := List.finRange n) (init := g 0))

      -- factor out the initial g 0
      have hpull :
          List.foldl (fun acc i => acc * g i.succ) (g 0) (List.finRange n)
            =
          g 0 * List.foldl (fun acc i => acc * g i.succ) 1 (List.finRange n) := by
        simpa using
          (List.foldl_mul_pull_out (h := fun i : Fin n => g i.succ)
            (a := g 0) (l := List.finRange n))

      -- IH applied to the tail function i ↦ g i.succ
      have hih :
          List.foldl (fun acc i => acc * g i.succ) 1 (List.finRange n)
            =
          (∏ i : Fin n, g i.succ) := by
        simpa using (foldl_finRange_mul_eq_prod (n := n) (g := fun i : Fin n => g i.succ))

      -- finish: rewrite foldl → product using hih, then use Fin.prod_univ_succ
      calc
        List.foldl (fun acc j => acc * g j) (g 0) (List.map Fin.succ (List.finRange n))
            =
        List.foldl (fun acc i => acc * g i.succ) (g 0) (List.finRange n) := hmap
        _ =
        g 0 * List.foldl (fun acc i => acc * g i.succ) 1 (List.finRange n) := hpull
        _ =
        g 0 * (∏ i : Fin n, g i.succ) := by
              -- bridge the foldl tail to the product tail
              simp [hih]
        _ =
        (∏ i : Fin (n + 1), g i) := by
              -- reverse of `∏ i, g i = g 0 * ∏ i, g i.succ`
              simpa using (Fin.prod_univ_succ (f := g)).symm

lemma extract_exp_var_i_eq_get {n : ℕ} (m : CPoly.CMvMonomial n) (x : Fin n) :
    extract_exp_var_i m x = Vector.get m x := by
  rfl

lemma eval₂_subst_monomial
  {𝔽 : Type _} {n : ℕ}
  [CommRing 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (vs : Fin n → CPoly.CMvPolynomial 1 𝔽)
  (m : CPoly.CMvMonomial n)
  (b : 𝔽) :
  CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
      (RingHom.id 𝔽) (fun _ : Fin 1 => b)
      (subst_monomial (n := n) (𝔽 := 𝔽) vs m)
    =
  CPoly.MonoR.evalMonomial (n := n) (R := 𝔽)
      (fun i =>
        CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
          (RingHom.id 𝔽) (fun _ : Fin 1 => b) (vs i))
      m := by
  classical
  -- Expand subst_monomial into the foldl product
  unfold subst_monomial

  -- Push eval₂ through the foldl product of powers
  have hfold :=
    CPoly.eval₂_foldl_mul_pow_univariate
      (𝔽 := 𝔽) (n := n) (vs := vs) (m := m) (b := b)
      (A := (CPoly.Lawful.C (n := 1) (R := 𝔽) (1 : 𝔽)))
      (L := List.finRange n)

  -- eval₂(C 1) = 1
  have hA :
      CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
          (RingHom.id 𝔽) (fun _ : Fin 1 => b)
          (CPoly.Lawful.C (n := 1) (R := 𝔽) (1 : 𝔽))
        = (1 : 𝔽) := by
    simpa using
      (CPoly.eval₂_Lawful_C (R := 𝔽) (S := 𝔽) (n := 1)
        (f := RingHom.id 𝔽) (vs := fun _ : Fin 1 => b) (c := (1 : 𝔽)))

  -- This is the exact foldl equality you already saw (keep Mul.mul in the fold body!)
  have hscalar :
      CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
          (RingHom.id 𝔽) (fun _ : Fin 1 => b)
          (List.foldl
            (fun acc i => Mul.mul acc (pow_univariate (vs i) (extract_exp_var_i m i)))
            (CPoly.Lawful.C (n := 1) (R := 𝔽) (1 : 𝔽))
            (List.finRange n))
        =
      List.foldl
        (fun acc i =>
          acc *
            (CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
                (RingHom.id 𝔽) (fun _ : Fin 1 => b) (vs i)) ^
              (extract_exp_var_i m i))
        1
        (List.finRange n) := by
    simpa [hA] using hfold

  -- Name the scalar values at b
  let vals : Fin n → 𝔽 :=
    fun i =>
      CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
        (RingHom.id 𝔽) (fun _ : Fin 1 => b) (vs i)

  -- Convert the RHS foldl into a ∏ using your new lemma
  have hprod :
      List.foldl (fun acc i => acc * (vals i) ^ (extract_exp_var_i m i)) 1 (List.finRange n)
        =
      (∏ i : Fin n, (vals i) ^ (extract_exp_var_i m i)) := by
    simpa [vals] using
      (foldl_finRange_mul_eq_prod (α := 𝔽) (n := n)
        (g := fun i : Fin n => (vals i) ^ (extract_exp_var_i m i)))

  -- Finish: rewrite hscalar into vals-form, rewrite via hprod, then match evalMonomial definition
  calc
    CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
        (RingHom.id 𝔽) (fun _ : Fin 1 => b)
        (List.foldl
          (fun acc i => Mul.mul acc (pow_univariate (vs i) (extract_exp_var_i m i)))
          (CPoly.Lawful.C (n := 1) (R := 𝔽) (1 : 𝔽))
          (List.finRange n))
        =
      List.foldl (fun acc i => acc * (vals i) ^ (extract_exp_var_i m i)) 1 (List.finRange n) := by
        simpa [vals] using hscalar
    _ =
      (∏ i : Fin n, (vals i) ^ (extract_exp_var_i m i)) := hprod
    _ =
      CPoly.MonoR.evalMonomial (n := n) (R := 𝔽) vals m := by
      -- Here is the only possible remaining mismatch: `extract_exp_var_i` vs `Vector.get`.
      -- If you have a lemma equating them, add it here (common name: `extract_exp_var_i_eq_get`).
      -- Otherwise, unfolding evalMonomial should show you exactly the exponent accessor.
      simp [CPoly.MonoR.evalMonomial, vals]
      simp [extract_exp_var_i_eq_get]

@[simp] lemma coe_Lawful_mul_CMvPolynomial_1
  {𝔽 : Type _} [CommRing 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (a : CPoly.Lawful 1 𝔽) (q : CPoly.CMvPolynomial 1 𝔽) :
  ((a * q : CPoly.Lawful 1 𝔽) : CPoly.CMvPolynomial 1 𝔽) =
    ((a : CPoly.CMvPolynomial 1 𝔽) * q) := by
  rfl

lemma lawful_coe_roundtrip[Zero 𝔽] (q : CPoly.CMvPolynomial 1 𝔽) :
  (show CPoly.CMvPolynomial 1 𝔽 from (show CPoly.Lawful 1 𝔽 from q)) = q := by rfl

lemma eval₂_mul_fun_CPoly
  {n : ℕ} {R S : Type}
  [CommSemiring R] [CommSemiring S]
  [DecidableEq R] [BEq R] [LawfulBEq R]
  (f : R →+* S) (vals : Fin n → S)
  (a b : CPoly.CMvPolynomial n R) :
  CPoly.CMvPolynomial.eval₂ (R := R) (S := S) (n := n) f vals (a * b)
    =
  CPoly.CMvPolynomial.eval₂ (R := R) (S := S) (n := n) f vals a *
  CPoly.CMvPolynomial.eval₂ (R := R) (S := S) (n := n) f vals b := by
  -- This is definitional/notation alignment only; it should be very fast.
  simp [(CPoly.eval₂_mul_fun (n := n) (R := R) (S := S) f vals a b)]

lemma CPoly.eval₂_add_fun
  {n : ℕ} {R S : Type}
  [CommSemiring R] [CommSemiring S]
  [DecidableEq R] [BEq R] [LawfulBEq R]
  (f : R →+* S) (vals : Fin n → S)
  (a b : CPoly.CMvPolynomial n R) :
  CPoly.CMvPolynomial.eval₂ (n := n) (R := R) (S := S) f vals (a + b)
    =
  CPoly.CMvPolynomial.eval₂ (n := n) (R := R) (S := S) f vals a
    +
  CPoly.CMvPolynomial.eval₂ (n := n) (R := R) (S := S) f vals b := by
  -- your existing lemma is in dot-form; this re-expresses it in function-form
  simp [(CPoly.eval₂_add (n := n) (R := R) (S := S) (f := f) (vals := vals) a b)]

@[simp] lemma c1_eq_Lawful_C
  {𝔽 : Type _} [CommRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽] (c : 𝔽) :
  (c1 (𝔽 := 𝔽) c) = (CPoly.Lawful.C (n := 1) (R := 𝔽) c) := by
  rfl

lemma Lawful_C_eq_c1
  {𝔽 : Type _} [CommRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (c : 𝔽) :
  (CPoly.Lawful.C (n := 1) (R := 𝔽) c : CPoly.CMvPolynomial 1 𝔽)
    =
  (c1 (𝔽 := 𝔽) c) := by
  rfl

lemma eval₂_eq_foldl
  {R S : Type _} {n : ℕ} [Semiring R] [CommSemiring S]
  [BEq R] [LawfulBEq R]
  (f : R →+* S) (vals : Fin n → S) (p : CPoly.CMvPolynomial n R) :
  CPoly.CMvPolynomial.eval₂ (R := R) (S := S) (n := n) f vals p
    =
  Std.ExtTreeMap.foldl
    (fun s m c => f c * CPoly.MonoR.evalMonomial vals m + s)
    0
    (p.1) := by
  -- just unfold your definition of eval₂
  simp [CPoly.CMvPolynomial.eval₂]

lemma eval₂_c1
  {𝔽 : Type _} [CommRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽] [DecidableEq 𝔽]
  (b c : 𝔽) :
  CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
      (RingHom.id 𝔽) (fun _ : Fin 1 => b) (c1 (𝔽 := 𝔽) c)
    = c := by
  -- turn c1 into Lawful.C, then use the library lemma
  -- CPoly.eval₂_Lawful_C gives = (RingHom.id 𝔽) c, which is definitional = c
  simpa [c1_eq_Lawful_C] using
    (CPoly.eval₂_Lawful_C (f := (RingHom.id 𝔽)) (vs := (fun _ : Fin 1 => b)) (c := c))

lemma eval₂_c1_mul_subst_add
  {𝔽 : Type _} {n : ℕ}
  [CommRing 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (vs : Fin n → CPoly.CMvPolynomial 1 𝔽)
  (b : 𝔽)
  (m : CPoly.CMvMonomial n)
  (c : 𝔽)
  (acc : CPoly.CMvPolynomial 1 𝔽) :
  CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
      (RingHom.id 𝔽) (fun _ : Fin 1 => b)
      ( @HAdd.hAdd _ _ _ instHAdd
          ( @HMul.hMul _ _ _ instHMul (c1 (𝔽 := 𝔽) c) (subst_monomial vs m) )
          acc )
    =
  c * CPoly.MonoR.evalMonomial
        (fun i =>
          CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
              (RingHom.id 𝔽) (fun _ : Fin 1 => b) (vs i))
        m
    +
  CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
      (RingHom.id 𝔽) (fun _ : Fin 1 => b) acc := by
  classical

  -- Force the homogeneous operations
  let add1 : CPoly.CMvPolynomial 1 𝔽 → CPoly.CMvPolynomial 1 𝔽 → CPoly.CMvPolynomial 1 𝔽 :=
    fun A B => @HAdd.hAdd _ _ _ instHAdd A B
  let mul1 : CPoly.CMvPolynomial 1 𝔽 → CPoly.CMvPolynomial 1 𝔽 → CPoly.CMvPolynomial 1 𝔽 :=
    fun A B => @HMul.hMul _ _ _ instHMul A B

  -- rewrite goal in terms of add1/mul1
  change
    CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => b)
        (add1 (mul1 (c1 (𝔽 := 𝔽) c) (subst_monomial vs m)) acc)
      =
    c * CPoly.MonoR.evalMonomial
          (fun i =>
            CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => b) (vs i)) m
      +
    CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => b) acc

  -- eval₂ distributes over + (now it matches because add1 is homogeneous)
  have hadd :
      CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => b)
          (add1 (mul1 (c1 (𝔽 := 𝔽) c) (subst_monomial vs m)) acc)
        =
      CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => b)
          (mul1 (c1 (𝔽 := 𝔽) c) (subst_monomial vs m))
      +
      CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => b) acc := by
    simpa [add1] using
      (CPoly.eval₂_add_fun
        (n := 1) (R := 𝔽) (S := 𝔽)
        (f := RingHom.id 𝔽) (vals := (fun _ : Fin 1 => b))
        (a := (mul1 (c1 (𝔽 := 𝔽) c) (subst_monomial vs m)))
        (b := acc))

  -- eval₂ distributes over * (matches because mul1 is homogeneous)
  have hmul :
      CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => b)
          (mul1 (c1 (𝔽 := 𝔽) c) (subst_monomial vs m))
        =
      (CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => b) (c1 (𝔽 := 𝔽) c))
        *
      (CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => b) (subst_monomial vs m)) := by
    simpa [mul1] using
      (eval₂_mul_fun_CPoly
        (n := 1) (R := 𝔽) (S := 𝔽)
        (f := RingHom.id 𝔽) (vals := (fun _ : Fin 1 => b))
        (a := (c1 (𝔽 := 𝔽) c)) (b := (subst_monomial vs m)))

  -- eval₂(c1 c) = c (go one-way to Lawful.C to avoid simp loop)
  have hc :
      CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => b) (c1 (𝔽 := 𝔽) c) = c := by
    rw [c1_eq_Lawful_C (𝔽 := 𝔽) (c := c)]
    simpa using
      (CPoly.eval₂_Lawful_C
        (n := 1) (R := 𝔽) (S := 𝔽)
        (f := RingHom.id 𝔽) (vs := (fun _ : Fin 1 => b)) (c := c))

  -- eval₂(subst_monomial vs m) = evalMonomial(...)
  have hs :
      CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => b) (subst_monomial vs m)
        =
      CPoly.MonoR.evalMonomial
        (fun i => CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => b) (vs i))
        m := by
    simpa using (eval₂_subst_monomial (vs := vs) (m := m) (b := b))

  -- assemble using rw (not simpa [hmul]) so we don't trigger rewriting to Lawful.C
  calc
    CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => b)
        (add1 (mul1 (c1 (𝔽 := 𝔽) c) (subst_monomial vs m)) acc)
        =
      CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => b)
          (mul1 (c1 (𝔽 := 𝔽) c) (subst_monomial vs m))
      +
      CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => b) acc := by
        exact hadd
    _ =
      (CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => b) (c1 (𝔽 := 𝔽) c))
        *
      (CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => b) (subst_monomial vs m))
      +
      CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => b) acc := by
        rw [hmul]
    _ =
      c * CPoly.MonoR.evalMonomial
            (fun i => CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => b) (vs i)) m
      +
      CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => b) acc := by
        rw [hc, hs]

lemma eval₂_foldl_step_eq_foldl_g
  {𝔽 : Type _} {n : ℕ}
  [CommRing 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (vs : Fin n → CPoly.CMvPolynomial 1 𝔽)
  (b : 𝔽)
  (pt : Fin n → 𝔽)
  (g : 𝔽 → (CPoly.CMvMonomial n × 𝔽) → 𝔽)
  (step : CPoly.CMvPolynomial 1 𝔽 → (CPoly.CMvMonomial n × 𝔽) → CPoly.CMvPolynomial 1 𝔽)
  (hstep :
    ∀ (acc : CPoly.CMvPolynomial 1 𝔽) (mc : CPoly.CMvMonomial n × 𝔽),
      CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => b) (step acc mc)
        =
      g (CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => b) acc) mc)
  :
  ∀ (l : List (CPoly.CMvMonomial n × 𝔽)) (acc : CPoly.CMvPolynomial 1 𝔽),
    CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => b)
        (List.foldl step acc l)
      =
    List.foldl g
      (CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => b) acc)
      l := by
  intro l acc
  induction l generalizing acc with
  | nil =>
      simp
  | cons mc tl ih =>
      simp [List.foldl, ih, hstep]

def step_fun
  {𝔽 : Type _} {n : ℕ}
  [CommRing 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (vs : Fin n → CPoly.CMvPolynomial 1 𝔽) :
  CPoly.CMvPolynomial 1 𝔽 → (CPoly.CMvMonomial n × 𝔽) → CPoly.CMvPolynomial 1 𝔽 :=
fun acc mc =>
  (@HAdd.hAdd _ _ _ instHAdd
    (@HMul.hMul _ _ _ instHMul
      (c1 (𝔽 := 𝔽) mc.2)
      (subst_monomial vs mc.1))
    acc)

lemma step_def
  {𝔽 : Type _} {n : ℕ}
  [CommRing 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (vs : Fin n → CPoly.CMvPolynomial 1 𝔽) :
  step_fun (𝔽 := 𝔽) (n := n) vs
    =
    (fun acc mc =>
      (@HAdd.hAdd _ _ _ instHAdd
        (@HMul.hMul _ _ _ instHMul (c1 (𝔽 := 𝔽) mc.2) (subst_monomial vs mc.1))
        acc)) := by
  rfl

@[simp] lemma toList_coe_CMvPolynomial
  {𝔽 : Type _} {n : ℕ}
  [CommRing 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽) :
  Std.ExtTreeMap.toList (p.1) = p.1.toList := by
  rfl

lemma eval_eq_foldl_toList
  {𝔽 : Type _} {n : ℕ}
  [CommRing 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (pt : Fin n → 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (g : 𝔽 → (CPoly.CMvMonomial n × 𝔽) → 𝔽)
  (hg :
    g = (fun s mc => s + mc.2 * CPoly.MonoR.evalMonomial pt mc.1))
  :
  CPoly.CMvPolynomial.eval pt p
    =
  List.foldl g 0 (p.1.toList) := by
  subst hg
  simp [CPoly.CMvPolynomial.eval]
  rw [eval₂_eq_foldl (f := RingHom.id 𝔽) (vals := pt) (p := p)]
  have hf :=
    (Std.ExtTreeMap.foldl_eq_foldl_toList
      (t := p.1)
      (f := fun s m c => (RingHom.id 𝔽) c * CPoly.MonoR.evalMonomial pt m + s)
      (init := (0 : 𝔽)))
  simpa [add_comm, add_left_comm, add_assoc, mul_assoc, mul_comm, mul_left_comm] using hf


lemma eval₂_eval₂Poly_c1
  {𝔽 : Type _} {n : ℕ}
  [CommRing 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽)
  (vs : Fin n → CPoly.CMvPolynomial 1 𝔽)
  (b : 𝔽) :
  CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
      (RingHom.id 𝔽) (fun _ : Fin 1 => b)
      (CPoly.eval₂Poly (𝔽 := 𝔽) (n := n) c1 vs p)
    =
  CPoly.CMvPolynomial.eval
      (fun i =>
        CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
            (RingHom.id 𝔽) (fun _ : Fin 1 => b) (vs i))
      p := by
  sorry


lemma honest_last_round
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [DecidableEq 𝔽] [Fintype 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽) (r : Fin n → 𝔽) (i : Fin n)
  (hlast : i.val.succ = n) :
  next_claim (𝔽 := 𝔽) (round_challenge := r i) (honest_round_poly (p := p) (ch := r) i)
    = CPoly.CMvPolynomial.eval r p := by
  sorry

lemma honest_step_round
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽) (r : Fin n → 𝔽) (i : Fin n)
  (hlt : i.val.succ < n) :
  let j : Fin n := ⟨i.val.succ, hlt⟩
  CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (0 : 𝔽))
      (honest_round_poly (p := p) (ch := r) j)
    +
    CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (1 : 𝔽))
      (honest_round_poly (p := p) (ch := r) j)
    =
    next_claim (𝔽 := 𝔽) (round_challenge := r i) (honest_round_poly (p := p) (ch := r) i) := by
  sorry

lemma accepts_and_bad_implies_exists_round_disagree_but_agree
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (claim : 𝔽) (p : CPoly.CMvPolynomial n 𝔽) (adv : Adversary 𝔽 n)
  (hfalse : claim ≠ true_sum (𝔽 := 𝔽) p)
  (r : Fin n → 𝔽) :
  AcceptsAndBadOnChallenges claim p adv r →
    ∃ i : Fin n, RoundDisagreeButAgreeAtChallenge (claim := claim) (p := p) (adv := adv) r i := by
  classical
  intro h
  rcases h with ⟨hAcc, hBad⟩
  let t : Transcript 𝔽 n := AdversaryTranscript claim p adv r

  -- pick the last bad round
  have hLast : LastBadRound (claim := claim) (p := p) (adv := adv) (r := r) := by
    exact badTranscript_implies_lastBadRound (claim := claim) (p := p) (adv := adv) (r := r) (by
      simpa [t] using hBad)

  rcases hLast with ⟨i, hi_bad, hi_after⟩
  refine ⟨i, ?_⟩

  have hneq : t.round_polys i ≠ honest_round_poly (p := p) (ch := r) i := by
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
      have hdec := acceptsEvent_final_ok (p := p) (t := t) hAcc
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
      -- note: we want the result in the same orientation as the goal; use `Eq.symm` if simp flips it.
      have := hfinal'.symm
      -- unfolding t / AdversaryTranscript puts t.challenges = r and t.claims (i.succ) = next_claim ...
      -- hsuc kills the `match` in derive_claims at i.succ
      -- `simp` may produce `eval r p = ...`; `simpa` below normalizes it to `... = eval r p`
      have htmp :
          CPoly.CMvPolynomial.eval r p =
            next_claim (𝔽 := 𝔽) (round_challenge := r i) (t.round_polys i) := by
        simpa [t, AdversaryTranscript, derive_claims, next_claim, hsuc] using this
      simpa [eq_comm] using htmp

    -- TODO (honest consistency for the last round):
    have honest_last :
        next_claim (𝔽 := 𝔽) (round_challenge := r i) (honest_round_poly (p := p) (ch := r) i)
          = CPoly.CMvPolynomial.eval r p := by
      admit

    -- Turn equality of next_claim into equality of eval₂.
    have hnc :
        next_claim (𝔽 := 𝔽) (round_challenge := r i) (t.round_polys i)
          =
        next_claim (𝔽 := 𝔽) (round_challenge := r i) (honest_round_poly (p := p) (ch := r) i) := by
      calc
        next_claim (𝔽 := 𝔽) (round_challenge := r i) (t.round_polys i)
            = CPoly.CMvPolynomial.eval r p := ht_claim_last
        _   = next_claim (𝔽 := 𝔽) (round_challenge := r i)
                (honest_round_poly (p := p) (ch := r) i) := by
              simpa using honest_last.symm

    refine ⟨hneq, ?_⟩
    simpa [next_claim] using hnc

  · -- not-last-round case
    have hlt : i.val.succ < n := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt i.isLt) hlast
    let j : Fin n := ⟨i.val.succ, hlt⟩

    have hj_honest : t.round_polys j = honest_round_poly (p := p) (ch := r) j := by
      have hij : i < j := by
        -- j.val = i.val.succ
        exact Fin.lt_iff_val_lt_val.mpr (Nat.lt_succ_self i.val)
      simpa [t, j] using hi_after j hij

    have hsum :
        CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (0 : 𝔽))
            (honest_round_poly (p := p) (ch := r) j)
          +
        CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (1 : 𝔽))
            (honest_round_poly (p := p) (ch := r) j)
          =
        t.claims (Fin.castSucc j) := by
      exact acceptsEvent_endpoints_sum_eq_claim_of_honest
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
      simp [t, AdversaryTranscript, derive_claims, next_claim, hsuc]

    have hclaim_j :
        t.claims (Fin.castSucc j)
          =
        next_claim (𝔽 := 𝔽) (round_challenge := r i) (t.round_polys i) := by
      simpa [hcast] using hclaim_i_succ

    -- TODO (honest step consistency):
    have honest_step :
        CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (0 : 𝔽))
            (honest_round_poly (p := p) (ch := r) j)
          +
        CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (1 : 𝔽))
            (honest_round_poly (p := p) (ch := r) j)
          =
        next_claim (𝔽 := 𝔽) (round_challenge := r i) (honest_round_poly (p := p) (ch := r) i) := by
      admit

    refine ⟨hneq, ?_⟩
    calc
      next_claim (𝔽 := 𝔽) (round_challenge := r i) (t.round_polys i)
          = t.claims (Fin.castSucc j) := by
              -- from hclaim_j : claims = next_claim, flip it
              simpa using (Eq.symm hclaim_j)
      _ =
          CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (0 : 𝔽))
            (honest_round_poly (p := p) (ch := r) j)
          +
          CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (1 : 𝔽))
            (honest_round_poly (p := p) (ch := r) j) := by
              simpa using hsum.symm
      _ = next_claim (𝔽 := 𝔽) (round_challenge := r i)
            (honest_round_poly (p := p) (ch := r) i) := honest_step

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

lemma sum_over_hypercube_recursive_zero
  {𝔽 β : Type _}
  (b0 b1 : 𝔽) (add : β → β → β)
  (F : (Fin 0 → 𝔽) → β) :
  sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β)
    (b0 := b0) (b1 := b1) (add := add) (m := 0) F
    =
  F (fun x : Fin 0 => nomatch x) := by
  -- unfold the recursion at m=0
  simp [sum_over_hypercube_recursive]
  -- remaining goal is just α-renaming of the empty function
  rfl

-- Helper: an “empty assignment” at the dependent type Fin (honest_num_open_vars i) → 𝔽
-- WITHOUT doing `cases hopen`.
noncomputable def empty_open_assignment
  {𝔽 : Type _} {n : ℕ} [Field 𝔽]
  (i : Fin n) (hopen : honest_num_open_vars (n := n) i = 0) :
  Fin (honest_num_open_vars (n := n) i) → 𝔽 :=
by
  -- build it at Fin 0, then transport along hopen.symm : 0 = honest_num_open_vars i
  refine Eq.ndrec (motive := fun m => Fin m → 𝔽) (fun x : Fin 0 => nomatch x) hopen.symm

lemma evalMonomial_monomial_x1
  {𝔽 : Type _} [CommSemiring 𝔽]
  (b : 𝔽) :
  CPoly.MonoR.evalMonomial (n := 1) (R := 𝔽)
      (fun _ : Fin 1 => b) (⟨#[1], by decide⟩ : CPoly.CMvMonomial 1)
    = b := by
  classical
  -- evalMonomial is ∏ i, vs i ^ m.get i; for n=1 this is just b^(m.get 0)=b^1=b
  simp [CPoly.MonoR.evalMonomial, pow_one]

@[simp] lemma eval₂_x0
  {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽]
  (b : 𝔽) :
  CPoly.CMvPolynomial.eval₂ (R := 𝔽) (S := 𝔽) (n := 1)
      (RingHom.id 𝔽) (fun _ : Fin 1 => b) (x0 (𝔽 := 𝔽))
    = b := by
  classical
  -- unfold x0 into the singleton map
  -- unfold eval₂ into foldl over that map
  simp [CPoly.CMvPolynomial.eval₂, x0]

  -- after the simp above, the goal should be exactly the foldl over an insert-empty tree
  -- apply your helper lemma to reduce the foldl
  -- then it remains to show evalMonomial of #[1] at (fun _ => b) is b
  --
  -- `simp` knows `pow_one`, and the product over Fin 1 is a singleton.
  -- if `simp` doesn't close it in your env, see the helper lemma below.
  simp [Std.ExtTreeMap.foldl_insert_empty, evalMonomial_monomial_x1]
