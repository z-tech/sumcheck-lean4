import Sumcheck.Src.CMvPolynomial
import Sumcheck.Src.HonestProver
import Sumcheck.Src.HonestTranscript
import Sumcheck.Src.Hypercube
import Sumcheck.Src.Verifier

import Sumcheck.Events.BadRound

import Sumcheck.Lemmas.Eval2

open scoped BigOperators

namespace Sumcheck

/-- evalMonomial for the monomial #[1] in arity 1. -/
lemma evalMonomial_monomial_x1
  {𝔽 : Type _} [CommSemiring 𝔽]
  (b : 𝔽) :
  CPoly.MonoR.evalMonomial (n := 1) (R := 𝔽)
      (fun _ : Fin 1 => b) (⟨#[1], by decide⟩ : CPoly.CMvMonomial 1)
    = b := by
  classical
  simp [CPoly.MonoR.evalMonomial, pow_one]

/-- This is the one that was failing for you: prove it by reducing the foldl on the singleton map. -/
@[simp] lemma eval₂_x0
  {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽]
  (b : 𝔽) :
  CPoly.CMvPolynomial.eval₂ (R := 𝔽) (S := 𝔽) (n := 1)
      (RingHom.id 𝔽) (fun _ : Fin 1 => b) (x0 (𝔽 := 𝔽))
    = b := by
  classical
  -- unfold x0 and eval₂
  simp [CPoly.CMvPolynomial.eval₂, x0]
  -- after simp, it’s exactly foldl over (∅.insert mon_x1 1)
  -- kill the foldl using your lemma from Lemmas/Eval2.lean
  simp [Std.ExtTreeMap.foldl_insert_empty, evalMonomial_monomial_x1]

lemma foldl_finRange_mul_eq_prod'
  {α : Type _} [CommMonoid α] :
  ∀ (n : ℕ) (g : Fin n → α) (s0 : α),
    List.foldl (fun s i => s * g i) s0 (List.finRange n)
      =
    s0 * ∏ i : Fin n, g i
| 0, g, s0 => by
    simp
| n+1, g, s0 => by
    classical
    simp [List.finRange_succ, List.foldl_map, Fin.prod_univ_succ]
    have h := foldl_finRange_mul_eq_prod' n (fun i : Fin n => g i.succ) (s0 * g 0)
    simpa [mul_assoc, mul_left_comm, mul_comm] using h

lemma foldl_finRange_mul_eq_prod
  {α : Type _} [CommMonoid α]
  (n : ℕ) (g : Fin n → α) :
  List.foldl (fun s i => s * g i) 1 (List.finRange n)
    =
  ∏ i : Fin n, g i := by
  simpa using (foldl_finRange_mul_eq_prod' (α := α) n g (1 : α))

lemma extract_exp_var_i_eq_get {n : ℕ} (m : CPoly.CMvMonomial n) (x : Fin n) :
    extract_exp_var_i m x = Vector.get m x := by
  rfl

/-- Copy of the working `eval₂_subst_monomial` proof pattern (avoids your stuck foldl/prod goal). -/
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
  unfold subst_monomial

  have hfold :=
    CPoly.eval₂_foldl_mul_pow_univariate
      (𝔽 := 𝔽) (n := n) (vs := vs) (m := m) (b := b)
      (A := (CPoly.Lawful.C (n := 1) (R := 𝔽) (1 : 𝔽)))
      (L := List.finRange n)

  have hA :
      CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
          (RingHom.id 𝔽) (fun _ : Fin 1 => b)
          (CPoly.Lawful.C (n := 1) (R := 𝔽) (1 : 𝔽))
        = (1 : 𝔽) := by
    simpa using
      (eval₂_Lawful_C
        (𝔽 := 𝔽) (n := 1)
        (f := RingHom.id 𝔽)
        (vs := fun _ : Fin 1 => b)
        (c := (1 : 𝔽)))

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

  let vals : Fin n → 𝔽 :=
    fun i =>
      CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
        (RingHom.id 𝔽) (fun _ : Fin 1 => b) (vs i)

  have hprod :
      List.foldl (fun acc i => acc * (vals i) ^ (extract_exp_var_i m i)) 1 (List.finRange n)
        =
      (∏ i : Fin n, (vals i) ^ (extract_exp_var_i m i)) := by
    simpa using (foldl_finRange_mul_eq_prod (α := 𝔽) (n := n)
      (g := fun i : Fin n => (vals i) ^ (extract_exp_var_i m i)))

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
      simp [CPoly.MonoR.evalMonomial, vals]
      simp [extract_exp_var_i_eq_get]

@[simp] lemma Fin.mk_eq_mk {n : ℕ} {a : ℕ} (h₁ h₂ : a < n) :
    (⟨a, h₁⟩ : Fin n) = ⟨a, h₂⟩ := by
  ext
  rfl

lemma honest_right_map_zero
  {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  {n : ℕ} (i : Fin n)
  (b : Fin (honest_num_open_vars (n := n) i) → 𝔽) :
  honest_right_map (𝔽 := 𝔽) (n := n) i b ⟨0, Nat.succ_pos _⟩
    = x0 (𝔽 := 𝔽) := by
  classical
  simp [honest_right_map]

lemma honest_right_map_zero'
  {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  {n : ℕ} (i : Fin n)
  (b : Fin (honest_num_open_vars (n := n) i) → 𝔽) :
  honest_right_map (𝔽 := 𝔽) (n := n) i b 0 = x0 (𝔽 := 𝔽) := by
  classical
  -- unfold and reduce the match on 0
  unfold honest_right_map
  rfl

lemma eval₂_honest_right_map_succ
  {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  {n : ℕ} (i : Fin n)
  (a : 𝔽)
  (b : Fin (honest_num_open_vars (n := n) i) → 𝔽)
  (t : Fin (honest_num_open_vars (n := n) i)) :
  CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
      (RingHom.id 𝔽) (fun _ : Fin 1 => a)
      (honest_right_map (𝔽 := 𝔽) (n := n) i b t.succ)
    = b t := by
  classical
  -- don't use Fin.cases here (t is Fin open, not Fin (open+1))
  cases t with
  | mk tv th =>
      -- now simp can reduce the match on tv.succ and the Fin.mk proof field mismatch vanishes
      simp [honest_right_map, Fin.succ, c1, CPoly.eval₂_Lawful_C]

lemma eval₂_honest_right_map
  {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  {n : ℕ} (i : Fin n)
  (a : 𝔽)
  (b : Fin (honest_num_open_vars (n := n) i) → 𝔽)
  (t : Fin (honest_num_open_vars (n := n) i + 1)) :
  CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
      (RingHom.id 𝔽) (fun _ : Fin 1 => a)
      (honest_right_map (𝔽 := 𝔽) (n := n) i b t)
    =
  Fin.cases a b t := by
  classical
  cases t using Fin.cases with
  | zero =>
      -- t = 0
      -- rewrite honest_right_map ... 0 = x0, then eval₂_x0
      rw [honest_right_map_zero' (𝔽 := 𝔽) (i := i) (b := b)]
      -- RHS is `a`
      simpa using (eval₂_x0 (𝔽 := 𝔽) a)
  | succ t =>
      -- t = succ t
      -- RHS is `b t`
      simpa using (eval₂_honest_right_map_succ (𝔽 := 𝔽) (i := i) (a := a) (b := b) (t := t))

lemma eval₂_addCases_honest_right_map
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (r : Fin n → 𝔽)
  (i : Fin n)
  (a : 𝔽)
  (b : Fin (honest_num_open_vars (n := n) i) → 𝔽)
  (j : Fin n) :
  CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
      (RingHom.id 𝔽) (fun _ : Fin 1 => a)
      (Fin.addCases
        (fun t : Fin i.val =>
          CPoly.Lawful.C (n := 1) (challenge_subset r i t))
        (honest_right_map (𝔽 := 𝔽) (n := n) i b)
        (Fin.cast (honest_split_eq (n := n) i).symm j))
    =
  Fin.addCases
    (fun t : Fin i.val => r ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩)
    (fun t : Fin (honest_num_open_vars (n := n) i + 1) => Fin.cases a b t)
    (Fin.cast (honest_split_eq (n := n) i).symm j) := by
  classical
  -- Case split on which side `Fin.addCases` takes.
  -- This produces exactly the two branches we want.
  cases h : (Fin.cast (honest_split_eq (n := n) i).symm j) using Fin.addCases with
  | left t =>
      -- left branch: we are evaluating a constant polynomial `C (...)`
      -- and RHS is the corresponding r ⟨t, _⟩.
      simp [Fin.addCases, CPoly.eval₂_Lawful_C, challenge_subset]
  | right t =>
      -- right branch: use your `eval₂_honest_right_map`
      -- RHS is `Fin.cases a b t`
      simpa [Fin.addCases, addCasesFun, h] using
        (eval₂_honest_right_map (𝔽 := 𝔽) (i := i) (a := a) (b := b)
          (t := t))

lemma eval₂_honest_combined_map_eq_addCasesFun
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (r : Fin n → 𝔽) (i : Fin n) (a : 𝔽)
  (b : Fin (honest_num_open_vars (n := n) i) → 𝔽) :
  (fun j : Fin n =>
      CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
        (RingHom.id 𝔽) (fun _ : Fin 1 => a)
        (honest_combined_map (𝔽 := 𝔽) (n := n) i (challenge_subset r i) b j))
  =
  (fun j : Fin n =>
      addCasesFun (α := 𝔽)
        (fun t : Fin i.val => r ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩)
        (fun t : Fin (honest_num_open_vars (n := n) i + 1) => Fin.cases a b t)
        (Fin.cast (honest_split_eq (n := n) i).symm j)) := by
  classical
  funext j
  -- unfold combined map (it is addCases of constants + honest_right_map)
  -- then apply your lemma
  simpa [honest_combined_map_def, addCasesFun] using
    (eval₂_addCases_honest_right_map (𝔽 := 𝔽) (r := r) (i := i) (a := a) (b := b) (j := j))


end Sumcheck
