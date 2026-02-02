import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Fold

import CompPoly.CMvPolynomial
import CompPoly.Lawful

import Std.Data.ExtTreeMap
import Std.Data.ExtTreeMap.Lemmas

import Sumcheck.Lemmas.Hypercube
import Sumcheck.Lemmas.ExtTreeMap
import Sumcheck.Src.CMvPolynomial
import Sumcheck.Src.HonestProver

lemma sumcheck_CMvMonomial_zero_get
  {n : ℕ} (x : Fin n) :
  (CPoly.CMvMonomial.zero (n := n)).get x = 0 := by
  -- CMvMonomial.zero = Vector.replicate n 0
  simp [CPoly.CMvMonomial.zero]

lemma sumcheck_evalMonomial_zero
  {S : Type} {n : ℕ} [CommSemiring S]
  (vs : Fin n → S) :
  CPoly.MonoR.evalMonomial (n := n) (R := S) vs (CPoly.CMvMonomial.zero (n := n)) = (1 : S) := by
  classical
  -- evalMonomial = ∏ i, vs i ^ m.get i ; and m.get i = 0 for the zero monomial.
  simp [CPoly.MonoR.evalMonomial, sumcheck_CMvMonomial_zero_get]

namespace CPoly

@[simp] lemma eval₂_Lawful_C
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
    exact
      Std.ExtTreeMap.foldl_empty
        (α := CPoly.CMvMonomial n) (β := R) (δ := S)
        (cmp := Ord.compare (α := CPoly.CMvMonomial n))
        (f := fun s m a => f a * CPoly.MonoR.evalMonomial vs m + s)
        (init := (0 : S))
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

lemma eval₂Poly_eq_list_foldl
  {n : ℕ} {𝔽 : Type _} [CommRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (f : 𝔽 → CPoly.CMvPolynomial 1 𝔽)
  (vs : Fin n → CPoly.CMvPolynomial 1 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽) :
  CPoly.eval₂Poly (n := n) (𝔽 := 𝔽) f vs p
    =
  List.foldl
    (fun acc (mc : CPoly.CMvMonomial n × 𝔽) =>
      @HAdd.hAdd _ _ _ instHAdd
        (@HMul.hMul _ _ _ instHMul (f mc.2) (subst_monomial vs mc.1))
        acc)
    (c1 (𝔽 := 𝔽) 0)
    p.1.toList := by
  classical
  simpa [CPoly.eval₂Poly] using
    (Std.ExtTreeMap.foldl_eq_foldl_toList
      (t := p.1)
      (f := fun acc m c =>
        @HAdd.hAdd _ _ _ instHAdd
          (@HMul.hMul _ _ _ instHMul (f c) (subst_monomial vs m))
          acc)
      (init := c1 (𝔽 := 𝔽) 0))

@[simp] lemma eval₂_add
  {n : ℕ} {R S : Type}
  [CommSemiring R] [CommSemiring S]
  [DecidableEq R] [BEq R] [LawfulBEq R]
  (f : R →+* S) (vals : Fin n → S)
  (a b : CMvPolynomial n R) :
  (a + b).eval₂ f vals = a.eval₂ f vals + b.eval₂ f vals := by
  classical
  -- move to MvPolynomial
  calc
    (a + b).eval₂ f vals
        = (fromCMvPolynomial (n := n) (R := R) (p := a + b)).eval₂ f vals := by
            simpa using (eval₂_equiv (n := n) (R := R) (S := S) (p := a + b) (f := f) (vals := vals))
    _   = (fromCMvPolynomial (n := n) (R := R) a +
            fromCMvPolynomial (n := n) (R := R) b).eval₂ f vals := by
            simp [map_add]
    _   = (fromCMvPolynomial (n := n) (R := R) a).eval₂ f vals +
          (fromCMvPolynomial (n := n) (R := R) b).eval₂ f vals := by
            -- eval₂ on MvPolynomial is a ring hom
          simp
    _   = a.eval₂ f vals + b.eval₂ f vals := by
            -- move back from MvPolynomial
            simp [eval₂_equiv (n := n) (R := R) (S := S) (p := a) (f := f) (vals := vals),
                  eval₂_equiv (n := n) (R := R) (S := S) (p := b) (f := f) (vals := vals)]

@[simp] lemma eval₂_mul
  {n : ℕ} {R S : Type}
  [CommSemiring R] [CommSemiring S]
  [DecidableEq R] [BEq R] [LawfulBEq R]
  (f : R →+* S) (vals : Fin n → S)
  (a b : CMvPolynomial n R) :
  (a * b).eval₂ f vals = a.eval₂ f vals * b.eval₂ f vals := by
  classical
  -- move to MvPolynomial
  calc
    (a * b).eval₂ f vals
        = (fromCMvPolynomial (n := n) (R := R) (p := a * b)).eval₂ f vals := by
            simpa using (eval₂_equiv (n := n) (R := R) (S := S) (p := a * b) (f := f) (vals := vals))
    _   = (fromCMvPolynomial (n := n) (R := R) a *
            fromCMvPolynomial (n := n) (R := R) b).eval₂ f vals := by
            simp [map_mul]
    _   = (fromCMvPolynomial (n := n) (R := R) a).eval₂ f vals *
          (fromCMvPolynomial (n := n) (R := R) b).eval₂ f vals := by
            -- eval₂ on MvPolynomial is a ring hom
            simp
    _   = a.eval₂ f vals * b.eval₂ f vals := by
            -- move back from MvPolynomial
            simp [eval₂_equiv (n := n) (R := R) (S := S) (p := a) (f := f) (vals := vals),
                  eval₂_equiv (n := n) (R := R) (S := S) (p := b) (f := f) (vals := vals)]

@[simp] lemma eval₂_mul_fun
  {n : ℕ} {R S : Type}
  [CommSemiring R] [CommSemiring S]
  [DecidableEq R] [BEq R] [LawfulBEq R]
  (f : R →+* S) (vals : Fin n → S)
  (a b : CMvPolynomial n R) :
  CMvPolynomial.eval₂ (n := n) (R := R) (S := S) f vals (a * b)
    =
  CMvPolynomial.eval₂ (n := n) (R := R) (S := S) f vals a *
  CMvPolynomial.eval₂ (n := n) (R := R) (S := S) f vals b := by
  classical
  -- move to MvPolynomial
  calc
    CMvPolynomial.eval₂ (n := n) (R := R) (S := S) f vals (a * b)
        =
      (fromCMvPolynomial (n := n) (R := R) (p := a * b)).eval₂ f vals := by
        -- `eval₂_equiv` is the bridge you already used in eval₂_add
        simpa using (eval₂_equiv (n := n) (R := R) (S := S) (p := a * b) (f := f) (vals := vals))
    _   =
      (fromCMvPolynomial (n := n) (R := R) a *
       fromCMvPolynomial (n := n) (R := R) b).eval₂ f vals := by
        simp [map_mul]
    _   =
      (fromCMvPolynomial (n := n) (R := R) a).eval₂ f vals *
      (fromCMvPolynomial (n := n) (R := R) b).eval₂ f vals := by
        simp
    _   =
      CMvPolynomial.eval₂ (n := n) (R := R) (S := S) f vals a *
      CMvPolynomial.eval₂ (n := n) (R := R) (S := S) f vals b := by
        simp [eval₂_equiv (n := n) (R := R) (S := S) (p := a) (f := f) (vals := vals),
              eval₂_equiv (n := n) (R := R) (S := S) (p := b) (f := f) (vals := vals)]

lemma eval₂_mul_Mul
  {n : ℕ} {R S : Type}
  [CommSemiring R] [CommSemiring S]
  [DecidableEq R] [BEq R] [LawfulBEq R]
  (f : R →+* S) (vals : Fin n → S)
  (a b : CMvPolynomial n R) :
  CMvPolynomial.eval₂ (n := n) (R := R) (S := S) f vals (Mul.mul a b)
    =
  CMvPolynomial.eval₂ (n := n) (R := R) (S := S) f vals a *
  CMvPolynomial.eval₂ (n := n) (R := R) (S := S) f vals b := by
  -- convert Mul.mul to (*) without simp
  dsimp [Mul.mul]
  exact eval₂_mul_fun (n := n) (R := R) (S := S) f vals a b

lemma eval₂_pow_univariate
  {𝔽 : Type} [CommRing 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (q : CMvPolynomial 1 𝔽) (b : 𝔽) :
  ∀ e : ℕ,
    CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
      (RingHom.id 𝔽) (fun _ : Fin 1 => b) (pow_univariate q e)
      =
    (CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
      (RingHom.id 𝔽) (fun _ : Fin 1 => b) q) ^ e
| 0 => by
    dsimp [pow_univariate]
    simp
| Nat.succ e => by
    let vs : Fin 1 → 𝔽 := fun _ => b
    -- unfold pow_univariate once; you said you changed it to use Mul.mul
    dsimp [pow_univariate]

    -- normalize the goal to use `vs` (avoids `fun x => b` matching problems)
    change
      CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
        (RingHom.id 𝔽) vs (Mul.mul q (pow_univariate q e))
        =
      (CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
        (RingHom.id 𝔽) vs q) ^ (e + 1)

    -- multiplicativity, *in Mul.mul form*
    rw [eval₂_mul_Mul (n := 1) (R := 𝔽) (S := 𝔽)
          (f := RingHom.id 𝔽) (vals := vs)
          (a := q) (b := pow_univariate q e)]

    -- IH, rewritten to use vs
    have ih := eval₂_pow_univariate (𝔽 := 𝔽) q b e
    have ih' :
      CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
        (RingHom.id 𝔽) vs (pow_univariate q e)
        =
      (CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
        (RingHom.id 𝔽) vs q) ^ e := by
      simpa [vs] using ih
    rw [ih']

    -- finish the power algebra
    set a : 𝔽 :=
      CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
        (RingHom.id 𝔽) vs q
    calc
      a * a ^ e = a ^ e * a := by simp [mul_comm]
      _ = a ^ (e + 1) := by simp [pow_succ]

@[simp] lemma eval₂_sum_over_hypercube_recursive
  {𝔽 : Type _} {m : ℕ}
  [CommSemiring 𝔽] [DecidableEq 𝔽]
  (b0 b1 : 𝔽)
  (vs : Fin 1 → 𝔽)
  (F : (Fin m → 𝔽) → CPoly.CMvPolynomial 1 𝔽) :
  CPoly.CMvPolynomial.eval₂ (R := 𝔽) (S := 𝔽) (n := 1) (RingHom.id 𝔽) vs
      (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := CPoly.CMvPolynomial 1 𝔽)
        b0 b1 (fun a b => a + b) (m := m) F)
    =
  sum_over_hypercube_recursive (𝔽 := 𝔽) (β := 𝔽)
    b0 b1 (fun a b => a + b) (m := m)
    (fun x =>
      CPoly.CMvPolynomial.eval₂ (R := 𝔽) (S := 𝔽) (n := 1) (RingHom.id 𝔽) vs (F x)) := by
  classical
  -- use the generic "map" lemma with g = eval₂
  refine
    (sum_over_hypercube_recursive_map
      (𝔽 := 𝔽) (β := CPoly.CMvPolynomial 1 𝔽) (γ := 𝔽)
      (b0 := b0) (b1 := b1)
      (addβ := fun a b => a + b)
      (addγ := fun a b => a + b)
      (g := fun p =>
        CPoly.CMvPolynomial.eval₂ (R := 𝔽) (S := 𝔽) (n := 1) (RingHom.id 𝔽) vs p)
      (hg := ?_)
      (m := m)
      (F := F))
  intro a b
  -- `eval₂` is a ring hom in the polynomial argument, so it preserves addition.
  -- This simp lemma name varies; one of these usually exists:
  --   `CPoly.CMvPolynomial.eval₂_add`, or `map_add`, or simp can do it after unfolding.
  simp

lemma eval₂_foldl_mul_pow_univariate
  {𝔽 : Type} [CommRing 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  {n : ℕ}
  (vs : Fin n → CPoly.CMvPolynomial 1 𝔽)
  (m : CPoly.CMvMonomial n)
  (b : 𝔽) :
  ∀ (A : CPoly.CMvPolynomial 1 𝔽) (L : List (Fin n)),
    CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
        (RingHom.id 𝔽) (fun _ : Fin 1 => b)
        (List.foldl
          (fun acc i => Mul.mul acc (pow_univariate (vs i) (extract_exp_var_i m i)))
          A L)
      =
    List.foldl
      (fun acc i =>
        acc *
          (CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
              (RingHom.id 𝔽) (fun _ : Fin 1 => b) (vs i)) ^
            (extract_exp_var_i m i))
      (CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
          (RingHom.id 𝔽) (fun _ : Fin 1 => b) A)
      L
  | A, [] => by
      simp [List.foldl]
  | A, i :: L => by
      have hp :
          CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
              (RingHom.id 𝔽) (fun _ : Fin 1 => b)
              (pow_univariate (vs i) (extract_exp_var_i m i))
            =
          (CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
              (RingHom.id 𝔽) (fun _ : Fin 1 => b) (vs i)) ^
            (extract_exp_var_i m i) := by
        simpa using eval₂_pow_univariate (𝔽 := 𝔽) (q := vs i) (b := b) (e := extract_exp_var_i m i)

      -- now eval₂_mul_Mul matches *definitionally*
      have hmul :
          CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
              (RingHom.id 𝔽) (fun _ : Fin 1 => b)
              (Mul.mul A (pow_univariate (vs i) (extract_exp_var_i m i)))
            =
          (CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
              (RingHom.id 𝔽) (fun _ : Fin 1 => b) A)
            *
          (CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
              (RingHom.id 𝔽) (fun _ : Fin 1 => b)
              (pow_univariate (vs i) (extract_exp_var_i m i))) := by
        simpa using
          (eval₂_mul_Mul
            (n := 1) (R := 𝔽) (S := 𝔽)
            (f := RingHom.id 𝔽) (vals := fun _ : Fin 1 => b)
            (a := A) (b := pow_univariate (vs i) (extract_exp_var_i m i)))

      -- unfold foldl once and apply IH on updated accumulator (which is Mul.mul A ...)
      simp [List.foldl, hmul, hp, eval₂_foldl_mul_pow_univariate]

@[simp] lemma CMvPolynomial_zero_val_eq_empty
  {n : ℕ} {R : Type _} [Zero R] [BEq R] [LawfulBEq R] :
  ((0 : CPoly.CMvPolynomial n R).1 : CPoly.Unlawful n R) =
    (Std.ExtTreeMap.empty : CPoly.Unlawful n R) := by
  classical
  simpa [CPoly.CMvPolynomial] using congrArg Subtype.val (CPoly.Lawful.zero_eq_empty (n := n) (R := R))

@[simp] lemma CMvPolynomial_eval₂_zero
  {R S : Type _} {n : ℕ} [Semiring R] [CommSemiring S]
  [BEq R] [LawfulBEq R]
  (f : R →+* S) (g : Fin n → S) :
  CPoly.CMvPolynomial.eval₂ (R := R) (S := S) (n := n) f g (0 : CPoly.CMvPolynomial n R) = 0 := by
  classical
  simp [CPoly.CMvPolynomial.eval₂, CMvPolynomial_zero_val_eq_empty]
