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
import Sumcheck.Lemmas.HonestProver
import Mathlib
import Sumcheck

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
  (b : 𝔽)
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

lemma eval₂Poly_eq_foldl_step_fun_c1
  {𝔽 : Type _} {n : ℕ}
  [CommRing 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽)
  (vs : Fin n → CPoly.CMvPolynomial 1 𝔽) :
  CPoly.eval₂Poly (𝔽 := 𝔽) (n := n) c1 vs p
    =
  List.foldl (step_fun (𝔽 := 𝔽) (n := n) vs) (c1 (𝔽 := 𝔽) 0) (p.1.toList) := by
  classical
  simpa [step_def] using
    (CPoly.eval₂Poly_eq_list_foldl (n := n) (𝔽 := 𝔽) (f := c1) (vs := vs) (p := p))

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
  classical

  let pt : Fin n → 𝔽 :=
    fun i =>
      CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
        (RingHom.id 𝔽) (fun _ : Fin 1 => b) (vs i)

  let g : 𝔽 → (CPoly.CMvMonomial n × 𝔽) → 𝔽 :=
    fun s mc => mc.2 * CPoly.MonoR.evalMonomial pt mc.1 + s

  have hg :
      g = (fun s mc => s + mc.2 * CPoly.MonoR.evalMonomial pt mc.1) := by
    funext s mc
    simp [g, add_comm]

  -- turn eval₂Poly into foldl step_fun
  have hpoly :
      CPoly.eval₂Poly (𝔽 := 𝔽) (n := n) c1 vs p
        =
      List.foldl (step_fun (𝔽 := 𝔽) (n := n) vs) (c1 (𝔽 := 𝔽) 0) (p.1.toList) :=
    eval₂Poly_eq_foldl_step_fun_c1 (𝔽 := 𝔽) (n := n) (p := p) (vs := vs)

  -- eval₂ commutes with one step
  have hstep :
      ∀ (acc : CPoly.CMvPolynomial 1 𝔽) (mc : CPoly.CMvMonomial n × 𝔽),
        CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
            (RingHom.id 𝔽) (fun _ : Fin 1 => b)
            (step_fun (𝔽 := 𝔽) (n := n) vs acc mc)
          =
        g
          (CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
            (RingHom.id 𝔽) (fun _ : Fin 1 => b) acc)
          mc := by
    intro acc mc
    -- this lemma is already in SoundnessAux.lean and matches step_fun's definition
    simpa [g, pt, step_def, step_fun, mul_assoc, add_assoc, add_comm, add_left_comm] using
      (eval₂_c1_mul_subst_add (𝔽 := 𝔽) (n := n)
        (vs := vs) (b := b) (m := mc.1) (c := mc.2) (acc := acc))

  -- initial accumulator evaluates to 0
  have hinit :
      CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
          (RingHom.id 𝔽) (fun _ : Fin 1 => b) (c1 (𝔽 := 𝔽) 0)
        =
      (0 : 𝔽) := by
    simp

  -- push eval₂ through the fold
  have hfold :
      CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
          (RingHom.id 𝔽) (fun _ : Fin 1 => b)
          (List.foldl (step_fun (𝔽 := 𝔽) (n := n) vs) (c1 (𝔽 := 𝔽) 0) (p.1.toList))
        =
      List.foldl g 0 (p.1.toList) := by
    simpa [hinit] using
      (eval₂_foldl_step_eq_foldl_g (𝔽 := 𝔽) (n := n)
        (b := b) (g := g)
        (step := step_fun (𝔽 := 𝔽) (n := n) vs)
        (hstep := hstep)
        (l := p.1.toList) (acc := c1 (𝔽 := 𝔽) 0))

  -- eval pt p is the same fold
  have heval :
      CPoly.CMvPolynomial.eval pt p = List.foldl g 0 (p.1.toList) := by
    simpa using
      (eval_eq_foldl_toList (𝔽 := 𝔽) (n := n) (pt := pt) (p := p) (g := g) (hg := hg))

  -- finish
  rw [hpoly]
  rw [hfold]
  simpa [pt] using heval.symm


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

-- transport sum_over_hypercube_recursive across m=0 without dependent rewrite pain
lemma sum_over_hypercube_recursive_eq_of_m_eq_zero
  {𝔽 β : Type _}
  (b0 b1 : 𝔽) (add : β → β → β)
  {m : ℕ} (hm : m = 0)
  (F : (Fin m → 𝔽) → β) :
  sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β)
    (b0 := b0) (b1 := b1) (add := add) (m := m) F
    =
  F (by
    -- build the empty function at Fin 0, then transport to Fin m via hm.symm
    refine Eq.ndrec (motive := fun k => Fin k → 𝔽) (fun x : Fin 0 => nomatch x) hm.symm) := by
  subst hm
  -- now m = 0 definitionally
  simp [sum_over_hypercube_recursive_zero]

lemma honest_last_round
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [DecidableEq 𝔽] [Fintype 𝔽]
  [BEq 𝔽] [LawfulBEq 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽) (r : Fin n → 𝔽) (i : Fin n)
  (hlast : i.val.succ = n) :
  next_claim (𝔽 := 𝔽) (round_challenge := r i)
      (honest_round_poly (p := p) (ch := r) i)
    =
  CPoly.CMvPolynomial.eval r p := by
  classical

  have hi : i.val + 1 = n := by
    simpa [Nat.succ_eq_add_one] using hlast

  have hopen : honest_num_open_vars (n := n) i = 0 := by
    simp [honest_num_open_vars, hi]

  -- define b0 at the dependent type via simp [hopen]
  let b0 : Fin (honest_num_open_vars (n := n) i) → 𝔽 :=
    empty_open_assignment (𝔽 := 𝔽) (n := n) i hopen

  -- last round => honest_round_poly is just F applied to the empty assignment
  have hround :
      honest_round_poly (p := p) (ch := r) i
        =
      CPoly.eval₂Poly (𝔽 := 𝔽) (n := n) c1
        (honest_combined_map (𝔽 := 𝔽) (n := n) i (challenge_subset r i) b0)
        p := by
    -- unfold to the hypercube sum
    simp [honest_round_poly, honest_prover_message_at_def]

    -- name the function being summed
    let F :
        (Fin (honest_num_open_vars (n := n) i) → 𝔽) → CPoly.CMvPolynomial 1 𝔽 :=
      fun b =>
        CPoly.eval₂Poly (𝔽 := 𝔽) (n := n) c1
          (honest_combined_map (𝔽 := 𝔽) (n := n) i (challenge_subset r i) b) p

    -- rewrite the goal *into* the shape the helper lemma produces, without `change`
    -- crucial: keep the same `add` that simp produced (it’s the CMvPolynomial instHAdd one)
    -- so we use `by` + `simpa [F]` to replace the anonymous function with `F`.
    have hcollapse :=
      sum_over_hypercube_recursive_eq_of_m_eq_zero
        (𝔽 := 𝔽) (β := CPoly.CMvPolynomial 1 𝔽)
        (b0 := (0 : 𝔽)) (b1 := (1 : 𝔽))
        (add := fun a b =>
          @HAdd.hAdd (CPoly.CMvPolynomial 1 𝔽) (CPoly.CMvPolynomial 1 𝔽)
            (CPoly.CMvPolynomial 1 𝔽) instHAdd a b)
        (m := honest_num_open_vars (n := n) i) (F := F) hopen

    -- now `hcollapse` is exactly: sum_over... F = F (ndrec empty)
    -- and your `b0` is exactly that transported empty function by definition.
    simpa [F, b0, empty_open_assignment] using hcollapse

  -- expand next_claim, rewrite by hround
  have hnc :
      next_claim (𝔽 := 𝔽) (round_challenge := r i)
          (honest_round_poly (p := p) (ch := r) i)
        =
      CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
        (RingHom.id 𝔽) (fun _ : Fin 1 => r i)
        (CPoly.eval₂Poly (𝔽 := 𝔽) (n := n) c1
          (honest_combined_map (𝔽 := 𝔽) (n := n) i (challenge_subset r i) b0) p) := by
    simp [next_claim, hround]

  have heval :
      CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
        (RingHom.id 𝔽) (fun _ : Fin 1 => r i)
        (CPoly.eval₂Poly (𝔽 := 𝔽) (n := n) c1
          (honest_combined_map (𝔽 := 𝔽) (n := n) i (challenge_subset r i) b0) p)
        =
      CPoly.CMvPolynomial.eval
        (fun j =>
          CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
            (RingHom.id 𝔽) (fun _ : Fin 1 => r i)
            (honest_combined_map (𝔽 := 𝔽) (n := n) i (challenge_subset r i) b0 j))
        p := by
    simpa using
      (eval₂_eval₂Poly_c1 (𝔽 := 𝔽) (n := n) (p := p)
        (vs := honest_combined_map (𝔽 := 𝔽) (n := n) i (challenge_subset r i) b0)
        (b := r i))

  have hpt :
      (fun j =>
        CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
          (RingHom.id 𝔽) (fun _ : Fin 1 => r i)
          (honest_combined_map (𝔽 := 𝔽) (n := n) i (challenge_subset r i) b0 j))
      =
      r := by
    funext j
    by_cases hj : j = i
    · subst hj
      -- key: combined_map at i is x0, and eval₂_x0 computes it
      have hcm :
          honest_combined_map (𝔽 := 𝔽) (n := n) j (challenge_subset r j) b0 j = x0 := by
        simpa using
          (honest_combined_map_at_i_is_x0 (𝔽 := 𝔽) (n := n)
            (i := j) (challenges := challenge_subset r j) (b := b0))

      -- now eval₂ of x0 at r j is r j
      simpa [hcm, x0] using (eval₂_x0 (𝔽 := 𝔽) (b := r j))
    ·
      -- j ≠ i, with i last => j.val < i.val
      have hjlt_succ : j.val < i.val.succ := by
        -- j.isLt : j.val < n
        -- hlast : i.val.succ = n  so  hlast.symm : n = i.val.succ
        exact (hlast.symm ▸ j.isLt)


      have hjle : j.val ≤ i.val := Nat.le_of_lt_succ hjlt_succ
      have hne : j.val ≠ i.val := by
        intro hEq
        apply hj
        ext
        exact hEq
      have hjlt : j.val < i.val := Nat.lt_of_le_of_ne hjle hne

      let t : Fin i.val := ⟨j.val, hjlt⟩

      -- cast the left index back to Fin n
      let j' : Fin n :=
        Fin.cast (honest_split_eq (n := n) i)
          (Fin.castAdd (honest_num_open_vars (n := n) i + 1) t)

      have hj' : j' = j := by
        ext
        simp [j', t]

      have hmap' :
          honest_combined_map (𝔽 := 𝔽) (n := n) i (challenge_subset r i) b0 j'
            =
          c1 (challenge_subset r i t) := by
        simpa [j'] using
          (honest_combined_map_left (𝔽 := 𝔽) (n := n)
            (i := i) (challenges := challenge_subset r i) (b := b0) (t := t))

      have hmap :
          honest_combined_map (𝔽 := 𝔽) (n := n) i (challenge_subset r i) b0 j
            =
          c1 (challenge_subset r i t) := by
        simpa [hj'] using hmap'

      have hc :
          CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
            (RingHom.id 𝔽) (fun _ : Fin 1 => r i)
            (c1 (challenge_subset r i t))
          =
          challenge_subset r i t := by
        simp

      have htj :
          (⟨t.val, Nat.lt_trans t.isLt i.isLt⟩ : Fin n) = j := by
        ext
        rfl

      simp [hmap, challenge_subset, htj]

  -- final assembly
  calc
    next_claim (𝔽 := 𝔽) (round_challenge := r i)
        (honest_round_poly (p := p) (ch := r) i)
        =
      CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
        (RingHom.id 𝔽) (fun _ : Fin 1 => r i)
        (CPoly.eval₂Poly (𝔽 := 𝔽) (n := n) c1
          (honest_combined_map (𝔽 := 𝔽) (n := n) i (challenge_subset r i) b0) p) := by
          exact hnc
    _ =
      CPoly.CMvPolynomial.eval
        (fun j =>
          CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
            (RingHom.id 𝔽) (fun _ : Fin 1 => r i)
            (honest_combined_map (𝔽 := 𝔽) (n := n) i (challenge_subset r i) b0 j))
        p := by
          exact heval
    _ =
      CPoly.CMvPolynomial.eval r p := by
          simp [hpt]

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
      simpa using (honest_last_round (p := p) (r := r) (i := i) hlast)


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
      -- `honest_step_round` introduces `j` via a `let`, so we `simpa [j]` to match your `j`.
      simpa [j] using (honest_step_round (p := p) (r := r) (i := i) hlt)

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

theorem degreeOf_mul_le_univariate {𝔽 : Type _} [CommSemiring 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
(a b : CPoly.CMvPolynomial 1 𝔽) :
  CPoly.CMvPolynomial.degreeOf (0 : Fin 1) (Mul.mul a b)
    ≤ CPoly.CMvPolynomial.degreeOf (0 : Fin 1) a + CPoly.CMvPolynomial.degreeOf (0 : Fin 1) b := by
  classical
  let i0 : Fin 1 := 0
  let A : MvPolynomial (Fin 1) 𝔽 := CPoly.fromCMvPolynomial (R := 𝔽) a
  let B : MvPolynomial (Fin 1) 𝔽 := CPoly.fromCMvPolynomial (R := 𝔽) b

  -- CPoly degreeOf = MvPolynomial degreeOf (at i0)
  have hEqA :
      CPoly.CMvPolynomial.degreeOf i0 a
        = MvPolynomial.degreeOf (σ := Fin 1) (R := 𝔽) i0 A := by
    simpa [A] using congrArg (fun f => f i0) (CPoly.degreeOf_equiv (p := a) (S := 𝔽))

  have hEqB :
      CPoly.CMvPolynomial.degreeOf i0 b
        = MvPolynomial.degreeOf (σ := Fin 1) (R := 𝔽) i0 B := by
    simpa [B] using congrArg (fun f => f i0) (CPoly.degreeOf_equiv (p := b) (S := 𝔽))

  have hEqAB :
      CPoly.CMvPolynomial.degreeOf i0 (Mul.mul a b)
        =
      MvPolynomial.degreeOf (σ := Fin 1) (R := 𝔽) i0 (CPoly.fromCMvPolynomial (R := 𝔽) (Mul.mul a b)) := by
    simpa using congrArg (fun f => f i0) (CPoly.degreeOf_equiv (p := Mul.mul a b) (S := 𝔽))

  -- Rewrite `fromCMvPolynomial (Mul.mul a b)` as `A * B`
  have hmap :
      CPoly.fromCMvPolynomial (R := 𝔽) (Mul.mul a b) = A * B := by
    -- Avoid `simp` here: `CPoly.map_mul` is itself a simp lemma and `simpa` would reduce to `True`.
    dsimp [A, B]
    change
      CPoly.fromCMvPolynomial (R := 𝔽) (a * b) =
        CPoly.fromCMvPolynomial (R := 𝔽) a * CPoly.fromCMvPolynomial (R := 𝔽) b
    exact CPoly.map_mul (a := a) (b := b) (R := 𝔽)

  -- Main MvPolynomial inequality
  have hMv :
      MvPolynomial.degreeOf (σ := Fin 1) (R := 𝔽) i0 (CPoly.fromCMvPolynomial (R := 𝔽) (Mul.mul a b))
        ≤
      MvPolynomial.degreeOf (σ := Fin 1) (R := 𝔽) i0 A + MvPolynomial.degreeOf (σ := Fin 1) (R := 𝔽) i0 B := by
    -- apply Mathlib on `A * B`, then rewrite by `hmap`
    -- `hmap` is oriented `from = A*B`, so we rewrite in the reverse direction.
    simpa [hmap] using
      (MvPolynomial.degreeOf_mul_le (R := 𝔽) (σ := Fin 1) i0 A B)

  -- transfer back to CPoly
  have : CPoly.CMvPolynomial.degreeOf i0 (Mul.mul a b)
      ≤ CPoly.CMvPolynomial.degreeOf i0 a + CPoly.CMvPolynomial.degreeOf i0 b := by
    simpa [hEqAB, hEqA, hEqB] using hMv

  simpa [i0] using this


theorem fromCMvPolynomial_c1_eq_C {𝔽 : Type _} [CommSemiring 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
(c : 𝔽) :
  CPoly.fromCMvPolynomial (R := 𝔽) (c1 (𝔽 := 𝔽) c)
    = (MvPolynomial.C c : MvPolynomial (Fin 1) 𝔽) := by
  classical
  ext m
  simp [CPoly.coeff_eq, c1, MvPolynomial.coeff_C, CPoly.Lawful.C, CPoly.CMvPolynomial.coeff,
    CPoly.Unlawful.C]
  by_cases hc : c = 0
  · simp [hc]
    change
      ((∅ : Std.ExtTreeMap (CPoly.CMvMonomial 1) 𝔽 (Ord.compare (α := CPoly.CMvMonomial 1)))[
          CPoly.CMvMonomial.ofFinsupp m]?).getD 0 = 0
    simp
  · simp [hc]
    have hz : ((CPoly.CMvMonomial.zero : CPoly.CMvMonomial 1)).toFinsupp = (0 : Fin 1 →₀ ℕ) := by
      ext i
      simp [CPoly.CMvMonomial.toFinsupp, CPoly.CMvMonomial.zero]
    by_cases hm : (0 : Fin 1 →₀ ℕ) = m
    · subst hm
      have hmono0 :
          CPoly.CMvMonomial.ofFinsupp (0 : Fin 1 →₀ ℕ) = (CPoly.CMvMonomial.zero : CPoly.CMvMonomial 1) := by
        apply CPoly.CMvMonomial.injective_toFinsupp
        simp [hz]
      change
        ((
            (∅ : Std.ExtTreeMap (CPoly.CMvMonomial 1) 𝔽 (Ord.compare (α := CPoly.CMvMonomial 1))).insert
              (CPoly.CMvMonomial.zero : CPoly.CMvMonomial 1) c)[
            CPoly.CMvMonomial.ofFinsupp (0 : Fin 1 →₀ ℕ)]?).getD 0 = c
      rw [hmono0]
      simpa using
        congrArg (fun o : Option 𝔽 => o.getD 0)
          (Std.ExtTreeMap.getElem?_insert_self
            (t := (∅ : Std.ExtTreeMap (CPoly.CMvMonomial 1) 𝔽 (Ord.compare (α := CPoly.CMvMonomial 1))))
            (k := (CPoly.CMvMonomial.zero : CPoly.CMvMonomial 1)) (v := c))
    · simp [hm]
      have hneq :
          CPoly.CMvMonomial.ofFinsupp m ≠ (CPoly.CMvMonomial.zero : CPoly.CMvMonomial 1) := by
        intro h
        apply hm
        have ht := congrArg (fun t => CPoly.CMvMonomial.toFinsupp t) h
        have hm0 : m = (0 : Fin 1 →₀ ℕ) := by
          simpa [hz] using ht
        exact hm0.symm
      haveI : Std.LawfulBEqOrd (CPoly.CMvMonomial 1) := by
        infer_instance
      haveI : LawfulBEq (CPoly.CMvMonomial 1) := by
        infer_instance
      have hcmp :
          compare (CPoly.CMvMonomial.zero : CPoly.CMvMonomial 1) (CPoly.CMvMonomial.ofFinsupp m) ≠ Ordering.eq := by
        intro h
        have hiff :
            compare (CPoly.CMvMonomial.zero : CPoly.CMvMonomial 1) (CPoly.CMvMonomial.ofFinsupp m) = Ordering.eq ↔
              ((CPoly.CMvMonomial.zero : CPoly.CMvMonomial 1) == CPoly.CMvMonomial.ofFinsupp m) := by
          simpa using
            (Std.LawfulBEqOrd.cmp_iff_beq
              (a := (CPoly.CMvMonomial.zero : CPoly.CMvMonomial 1))
              (b := CPoly.CMvMonomial.ofFinsupp m))
        have hbeq : ((CPoly.CMvMonomial.zero : CPoly.CMvMonomial 1) == CPoly.CMvMonomial.ofFinsupp m) :=
          hiff.1 h
        have hne' : (CPoly.CMvMonomial.zero : CPoly.CMvMonomial 1) ≠ CPoly.CMvMonomial.ofFinsupp m :=
          fun hEq => hneq hEq.symm
        exact (not_beq_of_ne hne') hbeq
      change
        ((
            (∅ : Std.ExtTreeMap (CPoly.CMvMonomial 1) 𝔽 (Ord.compare (α := CPoly.CMvMonomial 1))).insert
              (CPoly.CMvMonomial.zero : CPoly.CMvMonomial 1) c)[
            CPoly.CMvMonomial.ofFinsupp m]?).getD 0 = 0
      have hins :
          ((
              (∅ : Std.ExtTreeMap (CPoly.CMvMonomial 1) 𝔽 (Ord.compare (α := CPoly.CMvMonomial 1))).insert
                (CPoly.CMvMonomial.zero : CPoly.CMvMonomial 1) c)[
              CPoly.CMvMonomial.ofFinsupp m]?) =
            if compare (CPoly.CMvMonomial.zero : CPoly.CMvMonomial 1) (CPoly.CMvMonomial.ofFinsupp m) = Ordering.eq then
              some c
            else
              (∅ : Std.ExtTreeMap (CPoly.CMvMonomial 1) 𝔽 (Ord.compare (α := CPoly.CMvMonomial 1)))[
                CPoly.CMvMonomial.ofFinsupp m]? := by
        simpa using
          (Std.ExtTreeMap.getElem?_insert
            (t := (∅ : Std.ExtTreeMap (CPoly.CMvMonomial 1) 𝔽 (Ord.compare (α := CPoly.CMvMonomial 1))))
            (k := (CPoly.CMvMonomial.zero : CPoly.CMvMonomial 1)) (v := c) :
            ((
                (∅ : Std.ExtTreeMap (CPoly.CMvMonomial 1) 𝔽 (Ord.compare (α := CPoly.CMvMonomial 1))).insert
                  (CPoly.CMvMonomial.zero : CPoly.CMvMonomial 1) c)[
                CPoly.CMvMonomial.ofFinsupp m]?) =
              if compare (CPoly.CMvMonomial.zero : CPoly.CMvMonomial 1) (CPoly.CMvMonomial.ofFinsupp m) = Ordering.eq then
                some c
              else
                (∅ : Std.ExtTreeMap (CPoly.CMvMonomial 1) 𝔽 (Ord.compare (α := CPoly.CMvMonomial 1)))[
                  CPoly.CMvMonomial.ofFinsupp m]?)
      have hinsD := congrArg (fun o : Option 𝔽 => o.getD 0) hins
      simpa [hcmp] using hinsD.trans (by simp)

theorem degreeOf_c1_eq_zero {𝔽 : Type _} [CommSemiring 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
(c : 𝔽) :
  CPoly.CMvPolynomial.degreeOf (0 : Fin 1) (c1 (𝔽 := 𝔽) c) = 0 := by
  classical
  let i0 : Fin 1 := 0

  -- Bridge `CPoly.CMvPolynomial.degreeOf` to `MvPolynomial.degreeOf`.
  have hEq :
      CPoly.CMvPolynomial.degreeOf i0 (c1 (𝔽 := 𝔽) c)
        = MvPolynomial.degreeOf (σ := Fin 1) (R := 𝔽) i0
            (CPoly.fromCMvPolynomial (R := 𝔽) (c1 (𝔽 := 𝔽) c)) := by
    simpa using
      congrArg (fun f => f i0)
        (CPoly.degreeOf_equiv (p := c1 (𝔽 := 𝔽) c) (S := 𝔽))

  -- Rewrite to the `MvPolynomial` side and use `MvPolynomial.degreeOf_C`.
  rw [hEq]
  rw [fromCMvPolynomial_c1_eq_C (𝔽 := 𝔽) (c := c)]
  simpa [i0] using
    (MvPolynomial.degreeOf_C (σ := Fin 1) (R := 𝔽) (a := c) (x := i0))

theorem degreeOf_pow_univariate_le {𝔽 : Type _} [CommRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
(q : CPoly.CMvPolynomial 1 𝔽) :
  ∀ e : ℕ,
    CPoly.CMvPolynomial.degreeOf (0 : Fin 1) (pow_univariate (𝔽 := 𝔽) q e)
      ≤ e * CPoly.CMvPolynomial.degreeOf (0 : Fin 1) q := by
  intro e
  induction e with
  | zero =>
      have h0 :
          CPoly.CMvPolynomial.degreeOf (0 : Fin 1)
              (pow_univariate (𝔽 := 𝔽) q 0) = 0 := by
        simpa [pow_univariate] using
          (degreeOf_c1_eq_zero (𝔽 := 𝔽) (c := (1 : 𝔽)))
      -- goal is an inequality, but simp turns `≤ 0` into `= 0`
      simpa [h0]
  | succ e ih =>
      have hmul :=
        degreeOf_mul_le_univariate (𝔽 := 𝔽) q (pow_univariate (𝔽 := 𝔽) q e)
      have h1 :
          CPoly.CMvPolynomial.degreeOf (0 : Fin 1)
              (Mul.mul q (pow_univariate (𝔽 := 𝔽) q e))
            ≤
            CPoly.CMvPolynomial.degreeOf (0 : Fin 1) q +
              e * CPoly.CMvPolynomial.degreeOf (0 : Fin 1) q := by
        refine le_trans hmul ?_
        exact Nat.add_le_add_left ih (CPoly.CMvPolynomial.degreeOf (0 : Fin 1) q)
      have harith :
          CPoly.CMvPolynomial.degreeOf (0 : Fin 1) q +
              e * CPoly.CMvPolynomial.degreeOf (0 : Fin 1) q
            ≤
            Nat.succ e * CPoly.CMvPolynomial.degreeOf (0 : Fin 1) q := by
        -- rewrite the RHS using `succ_mul`, then commute the sum on the LHS
        -- to make it reflexive.
        simpa [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      have h2 := le_trans h1 harith
      simpa [pow_univariate] using h2

theorem fromCMvPolynomial_x0_eq_X {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽] :
  CPoly.fromCMvPolynomial (R := 𝔽) (x0 (𝔽 := 𝔽)) = (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) 𝔽) := by
  classical
  ext s
  simp [CPoly.coeff_eq, x0, CPoly.CMvPolynomial.coeff, MvPolynomial.coeff_X']
  set mon_x1 : CPoly.CMvMonomial 1 := { toArray := #[1], size_toArray := x0._proof_1 }
  have hmon_toF : CPoly.CMvMonomial.toFinsupp mon_x1 = (Finsupp.single (0 : Fin 1) 1) := by
    refine Finsupp.ext ?_
    intro i
    fin_cases i
    simp [CPoly.CMvMonomial.toFinsupp, mon_x1]
  have hmon : mon_x1 = CPoly.CMvMonomial.ofFinsupp (Finsupp.single (0 : Fin 1) 1) := by
    apply (CPoly.CMvMonomial.injective_toFinsupp (n := 1))
    simpa [hmon_toF]
  let t : Std.ExtTreeMap (CPoly.CMvMonomial 1) 𝔽 (Ord.compare (α := CPoly.CMvMonomial 1)) :=
    (∅ : Std.ExtTreeMap (CPoly.CMvMonomial 1) 𝔽 (Ord.compare (α := CPoly.CMvMonomial 1))).insert
      mon_x1 (1 : 𝔽)
  change t[CPoly.CMvMonomial.ofFinsupp s]?.getD 0 = if (fun₀ | 0 => 1) = s then 1 else 0
  by_cases h : CPoly.CMvMonomial.ofFinsupp s = mon_x1
  · have hs : (Finsupp.single (0 : Fin 1) 1) = s := by
      apply (CPoly.CMvMonomial.injective_ofFinsupp (n := 1))
      calc
        CPoly.CMvMonomial.ofFinsupp (Finsupp.single (0 : Fin 1) 1)
            = mon_x1 := by simpa [hmon]
        _ = CPoly.CMvMonomial.ofFinsupp s := by simpa using h.symm
    have hlookup : t[CPoly.CMvMonomial.ofFinsupp s]? = some (1 : 𝔽) := by
      simpa [t, h] using
        (Std.ExtTreeMap.getElem?_insert_self
          (t := (∅ : Std.ExtTreeMap (CPoly.CMvMonomial 1) 𝔽 (Ord.compare (α := CPoly.CMvMonomial 1))))
          (k := mon_x1) (v := (1 : 𝔽)))
    simp [hlookup, hs]
  · have hs : (Finsupp.single (0 : Fin 1) 1) ≠ s := by
      intro hs
      apply h
      have : CPoly.CMvMonomial.ofFinsupp s = CPoly.CMvMonomial.ofFinsupp (Finsupp.single (0 : Fin 1) 1) := by
        simpa [hs]
      exact this.trans hmon.symm
    have hne : mon_x1 ≠ CPoly.CMvMonomial.ofFinsupp s := by
      intro h'
      apply h
      simpa using h'.symm
    have hlookup : t[CPoly.CMvMonomial.ofFinsupp s]? = none := by
      -- unfold the insert-lookup formula and simplify
      simpa [t, Std.compare_eq_iff_eq, hne] using
        (Std.ExtTreeMap.getElem?_insert
          (t := (∅ : Std.ExtTreeMap (CPoly.CMvMonomial 1) 𝔽 (Ord.compare (α := CPoly.CMvMonomial 1))))
          (k := mon_x1) (v := (1 : 𝔽)) (a := CPoly.CMvMonomial.ofFinsupp s))
    simp [hlookup, hs]

theorem degreeOf_x0_le_one {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽] :
  CPoly.CMvPolynomial.degreeOf (0 : Fin 1) (x0 (𝔽 := 𝔽)) ≤ 1 := by
  classical
  -- sanity check: our helper axiom works
  have hx :
      CPoly.fromCMvPolynomial (R := 𝔽) (x0 (𝔽 := 𝔽))
        = (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) 𝔽) := by
    simpa using (fromCMvPolynomial_x0_eq_X (𝔽 := 𝔽))

  -- now translate CPoly.degreeOf to MvPolynomial.degreeOf
  let i0 : Fin 1 := 0
  have hEq :
      CPoly.CMvPolynomial.degreeOf i0 (x0 (𝔽 := 𝔽))
        =
      MvPolynomial.degreeOf (σ := Fin 1) (R := 𝔽) i0
        (CPoly.fromCMvPolynomial (R := 𝔽) (x0 (𝔽 := 𝔽))) := by
    simpa using
      congrArg (fun f => f i0) (CPoly.degreeOf_equiv (p := (x0 (𝔽 := 𝔽))) (S := 𝔽))

  have h : CPoly.CMvPolynomial.degreeOf i0 (x0 (𝔽 := 𝔽)) ≤ 1 := by
    rw [hEq]
    -- use the explicit rewrite first, then compute degree
    rw [hx]
    simpa [MvPolynomial.degreeOf_X, i0]

  simpa [i0] using h

theorem degree_subst_monomial_honest_combined_le_exp_i {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
(r : Fin n → 𝔽) (i : Fin n)
(b : Fin (honest_num_open_vars (n := n) i) → 𝔽)
(m : CPoly.CMvMonomial n) :
  CPoly.CMvPolynomial.degreeOf (0 : Fin 1)
      (subst_monomial (n := n) (𝔽 := 𝔽)
        (honest_combined_map (𝔽 := 𝔽) (n := n) i (challenge_subset r i) b) m)
    ≤ extract_exp_var_i m i := by
  classical
  -- set up abbreviations
  let vs : Fin n → CPoly.CMvPolynomial 1 𝔽 :=
    honest_combined_map (𝔽 := 𝔽) (n := n) i (challenge_subset r i) b
  let deg : CPoly.CMvPolynomial 1 𝔽 → ℕ :=
    fun q => CPoly.CMvPolynomial.degreeOf (0 : Fin 1) q
  let term : Fin n → CPoly.CMvPolynomial 1 𝔽 :=
    fun j => pow_univariate (𝔽 := 𝔽) (vs j) (extract_exp_var_i m j)
  let degPow : Fin n → ℕ := fun j => deg (term j)

  -- bound degree of a foldl product by degree(acc) + sum of degrees
  have hfold :
      ∀ (L : List (Fin n)) (acc : CPoly.CMvPolynomial 1 𝔽),
        deg (L.foldl (fun a j => Mul.mul a (term j)) acc)
          ≤ deg acc + ((L.map degPow).sum) := by
    intro L acc
    induction L generalizing acc with
    | nil =>
        simp [deg]
    | cons j L ih =>
        have ih' := ih (acc := Mul.mul acc (term j))
        have hmul : deg (Mul.mul acc (term j)) ≤ deg acc + deg (term j) := by
          simpa [deg] using (degreeOf_mul_le_univariate (a := acc) (b := term j))
        have h := le_trans ih' (Nat.add_le_add_right hmul _)
        simpa [List.foldl, List.map, degPow, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

  -- specialize to subst_monomial
  have hdeg_subst_le_list :
      deg (subst_monomial (n := n) (𝔽 := 𝔽) vs m)
        ≤ ((List.finRange n).map degPow).sum := by
    have h0 : deg (c1 (𝔽 := 𝔽) (1 : 𝔽)) = 0 := by
      simpa [deg] using (degreeOf_c1_eq_zero (𝔽 := 𝔽) (c := (1 : 𝔽)))
    have h := hfold (L := List.finRange n) (acc := c1 (𝔽 := 𝔽) (1 : 𝔽))
    have h' := h
    rw [h0] at h'
    simpa [subst_monomial, term, degPow, deg] using h'

  -- rewrite list sum as a Fintype sum
  have hsum_univ : (∑ j : Fin n, degPow j) = ((List.finRange n).map degPow).sum := by
    simpa using (Fin.sum_univ_def (n := n) (f := degPow))

  have hdeg_subst_le_sum :
      deg (subst_monomial (n := n) (𝔽 := 𝔽) vs m) ≤ ∑ j : Fin n, degPow j := by
    have hsum_univ' : ((List.finRange n).map degPow).sum = ∑ j : Fin n, degPow j := by
      simpa using hsum_univ.symm
    simpa [hsum_univ'] using hdeg_subst_le_list

  -- show deg (vs j) = 0 for j ≠ i
  have hdeg_vs_other : ∀ j : Fin n, j ≠ i → deg (vs j) = 0 := by
    intro j hj
    have hdef :=
      (honest_combined_map_def (𝔽 := 𝔽) (n := n) (i := i)
        (challenges := challenge_subset r i) (b := b) (j := j))
    have hcast :
        vs j =
          Fin.addCases (m := i.val) (n := honest_num_open_vars (n := n) i + 1)
            (motive := fun _ => CPoly.CMvPolynomial 1 𝔽)
            (fun t : Fin i.val => c1 (𝔽 := 𝔽) (challenge_subset r i t))
            (honest_right_map (𝔽 := 𝔽) (n := n) i b)
            (Fin.cast (honest_split_eq (n := n) i).symm j) := by
      simpa [vs] using hdef
    rw [hcast]
    cases h : (Fin.cast (honest_split_eq (n := n) i).symm j) using Fin.addCases with
    | left t =>
        simpa [Fin.addCases, h, deg] using
          (degreeOf_c1_eq_zero (𝔽 := 𝔽) (c := challenge_subset r i t))
    | right t =>
        -- simplify the goal but keep the equation `h` around
        simp [Fin.addCases, h]
        cases t using Fin.cases with
        | zero =>
            exfalso
            have hjEq : j = i := by
              have := congrArg (Fin.cast (honest_split_eq (n := n) i)) h
              simpa [honest_current_index_eq (n := n) i] using this
            exact hj hjEq
        | succ t' =>
            cases t' with
            | mk tv htv =>
                simpa [deg, honest_right_map] using
                  (degreeOf_c1_eq_zero (𝔽 := 𝔽) (c := b ⟨tv, htv⟩))

  -- show degPow j = 0 for j ≠ i
  have hdegPow_other : ∀ j : Fin n, j ≠ i → degPow j = 0 := by
    intro j hj
    have hpow : degPow j ≤ (extract_exp_var_i m j) * deg (vs j) := by
      simpa [degPow, deg] using
        (degreeOf_pow_univariate_le (𝔽 := 𝔽) (q := vs j) (extract_exp_var_i m j))
    have hdeg0 : deg (vs j) = 0 := hdeg_vs_other j hj
    have : degPow j ≤ 0 := by
      simpa [hdeg0] using hpow
    exact Nat.eq_zero_of_le_zero this

  -- collapse the Fintype sum to the single i-term
  have hsum_single : (∑ j : Fin n, degPow j) = degPow i := by
    classical
    refine (Fintype.sum_eq_single (a := i) (f := degPow) ?_)
    intro j hj
    exact hdegPow_other j hj

  -- bound the i-term by the exponent
  have hdegPow_i : degPow i ≤ extract_exp_var_i m i := by
    have hxi : vs i = x0 (𝔽 := 𝔽) := by
      simpa [vs] using
        (honest_combined_map_at_i_is_x0 (𝔽 := 𝔽) (n := n) (i := i)
          (challenges := challenge_subset r i) (b := b))
    have hpow : degPow i ≤ (extract_exp_var_i m i) * deg (vs i) := by
      simpa [degPow, deg] using
        (degreeOf_pow_univariate_le (𝔽 := 𝔽) (q := vs i) (extract_exp_var_i m i))
    have hx0 : deg (vs i) ≤ 1 := by
      simpa [deg, hxi] using (degreeOf_x0_le_one (𝔽 := 𝔽))
    have hmul : (extract_exp_var_i m i) * deg (vs i) ≤ extract_exp_var_i m i := by
      simpa [Nat.mul_one] using (Nat.mul_le_mul_left (extract_exp_var_i m i) hx0)
    exact le_trans hpow hmul

  -- final assembly
  have :
      deg (subst_monomial (n := n) (𝔽 := 𝔽) vs m) ≤ extract_exp_var_i m i := by
    calc
      deg (subst_monomial (n := n) (𝔽 := 𝔽) vs m)
          ≤ ∑ j : Fin n, degPow j := hdeg_subst_le_sum
      _ = degPow i := hsum_single
      _ ≤ extract_exp_var_i m i := hdegPow_i

  simpa [degPow, deg, term, vs] using this

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
  prob_over_challenges (𝔽 := 𝔽) (n := n + 1) E ≤ (d : ℚ) / count_field_size (𝔽 := 𝔽) := by
  classical
  -- unfold the probability definition
  simp [prob_over_challenges, all_assignments_n, count_field_size]

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
        simpa using (Fin.insertNth_self_removeNth (p := i) (f := r))
      have hsrec : Fin.insertNth i (s i) (Fin.removeNth i s) = s := by
        simpa using (Fin.insertNth_self_removeNth (p := i) (f := s))
      calc
        r = Fin.insertNth i (r i) (Fin.removeNth i r) := by simpa [hrrec]
        _ = Fin.insertNth i (s i) (Fin.removeNth i s) := by simpa [hrest, ha]
        _ = s := by simpa [hsrec]

    exact Finset.card_le_card_of_injOn g hg_maps hg_inj

  have hS_card : S.card = ∑ rRest : (Fin n → 𝔽), (fiber rRest).card := by
    classical
    simpa [S] using (Finset.card_sigma (s := (Finset.univ : Finset (Fin n → 𝔽)))
      (t := fun rRest => fiber rRest))

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
      simpa [Nat.mul_comm] using hconst
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
    simp [Fintype.card_pi_const, pow_succ, mul_assoc, mul_left_comm, mul_comm]

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
      AcceptsAndBadOnChallenges claim p adv r ∧
      RoundDisagreeButAgreeAtChallenge (claim := claim) (p := p) (adv := adv) r i)
    ≤ (max_ind_degree p) / count_field_size (𝔽 := 𝔽) := by
  classical
  cases n with
  | zero =>
      exact (Fin.elim0 i)
  | succ n' =>
      classical
      let E : (Fin (n' + 1) → 𝔽) → Prop := fun r =>
        AcceptsAndBadOnChallenges claim p adv r ∧
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
        · simpa [S, hS]
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
            simpa [hg_eq a0, hh_eq a0, hgh]

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
                · simp [agreeF]
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
                  / (count_field_size (𝔽 := 𝔽) : ℚ) := by
              -- unfold prob_agreement_at_random_challenge
              simpa [prob_agreement_at_random_challenge] using hprob

            have hdenom : count_all_assignments_n (𝔽 := 𝔽) 1 = count_field_size (𝔽 := 𝔽) := by
              simp [count_all_assignments_n, count_field_size, all_assignments_n, Fintype.card_pi_const]

            have hprob'' :
                (count_assignments_causing_agreement g h : ℚ) / (count_field_size (𝔽 := 𝔽) : ℚ)
                  ≤
                (MvPolynomial.degreeOf (⟨0, by decide⟩ : Fin 1) (difference_poly g h) : ℚ)
                  / (count_field_size (𝔽 := 𝔽) : ℚ) := by
              simpa [hdenom] using hprob'

            have hpos : 0 < (count_field_size (𝔽 := 𝔽) : ℚ) := by
              have : 0 < count_field_size (𝔽 := 𝔽) := by
                simpa [count_field_size] using (Fintype.card_pos_iff.2 ⟨(0 : 𝔽)⟩)
              exact_mod_cast this

            have hne : (count_field_size (𝔽 := 𝔽) : ℚ) ≠ 0 := ne_of_gt hpos

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
              simpa [r] using (Fin.insertNth_apply_same (i := i) (x := (a : 𝔽)) (p := rRest))
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
          AcceptsAndBadOnChallenges claim p adv r ∧
          RoundDisagreeButAgreeAtChallenge (claim := claim) (p := p) (adv := adv) r i))
    ≤ n * (max_ind_degree p) / count_field_size (𝔽 := 𝔽) := by
  classical
  -- Sum the pointwise bounds.
  have hsum :
      (∑ i : Fin n,
          prob_over_challenges (𝔽 := 𝔽) (n := n)
            (fun r =>
              AcceptsAndBadOnChallenges claim p adv r ∧
              RoundDisagreeButAgreeAtChallenge (claim := claim) (p := p) (adv := adv) r i))
        ≤ ∑ i : Fin n, ((max_ind_degree p : ℚ) / (count_field_size (𝔽 := 𝔽) : ℚ)) := by
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
            AcceptsAndBadOnChallenges claim p adv r ∧
            RoundDisagreeButAgreeAtChallenge (claim := claim) (p := p) (adv := adv) r i))
        ≤ ∑ i : Fin n, ((max_ind_degree p : ℚ) / (count_field_size (𝔽 := 𝔽) : ℚ)) := hsum
    _ = (n : ℚ) * ((max_ind_degree p : ℚ) / (count_field_size (𝔽 := 𝔽) : ℚ)) := by
      -- sum of a constant over `Fin n`
      simp
    _ = n * (max_ind_degree p) / count_field_size (𝔽 := 𝔽) := by
      -- put it back in the form used by the statement
      simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
