import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Fold

import CompPoly.CMvPolynomial
import CompPoly.Lawful

import Std.Data.ExtTreeMap
import Std.Data.ExtTreeMap.Lemmas
import ExtTreeMapLemmas.ExtTreeMap

import Sumcheck.Lemmas.Hypercube
import Sumcheck.Src.CMvPolynomial
import Sumcheck.Src.HonestProver

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
            simpa using
              (map_add (MvPolynomial.eval₂Hom (σ := Fin n) f vals)
                (fromCMvPolynomial (n := n) (R := R) a)
                (fromCMvPolynomial (n := n) (R := R) b))
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
            simpa using
              (map_mul (MvPolynomial.eval₂Hom (σ := Fin n) f vals)
                (fromCMvPolynomial (n := n) (R := R) a)
                (fromCMvPolynomial (n := n) (R := R) b))
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
        simpa using
          (map_mul (MvPolynomial.eval₂Hom (σ := Fin n) f vals)
            (fromCMvPolynomial (n := n) (R := R) a)
            (fromCMvPolynomial (n := n) (R := R) b))
    _   =
      CMvPolynomial.eval₂ (n := n) (R := R) (S := S) f vals a *
      CMvPolynomial.eval₂ (n := n) (R := R) (S := S) f vals b := by
        simp [eval₂_equiv (n := n) (R := R) (S := S) (p := a) (f := f) (vals := vals),
              eval₂_equiv (n := n) (R := R) (S := S) (p := b) (f := f) (vals := vals)]

lemma lawful_coe_roundtrip
  {𝔽 : Type} [CommRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (q : CPoly.CMvPolynomial 1 𝔽) :
  (show CPoly.CMvPolynomial 1 𝔽 from (show CPoly.Lawful 1 𝔽 from q)) = q := by
  rfl

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
    simpa [c1] using
      (eval₂_Lawful_C
        (𝔽 := 𝔽) (n := 1)
        (f := RingHom.id 𝔽)
        (vs := fun _ : Fin 1 => b)
        (c := (1 : 𝔽)))
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

/-- `eval₂` commutes with `sum_over_hypercube_recursive` when `add` is `+`. -/
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
  simpa using (eval₂_add
    (R := 𝔽) (S := 𝔽) (n := 1) (f := (RingHom.id 𝔽)) (vs := vs) a b)

lemma List.foldl_mul_assoc
  {α : Type} [CommMonoid α] :
  ∀ (a b : α) (xs : List α),
    List.foldl (fun acc x => acc * x) (a * b) xs
      =
    a * List.foldl (fun acc x => acc * x) b xs
| a, b, [] => by
    simp [List.foldl]
| a, b, x :: xs => by
    -- foldl f (a*b) (x::xs) = foldl f ((a*b)*x) xs
    -- RHS = a * foldl f (b*x) xs
    -- use commutativity/associativity to rewrite ((a*b)*x) = a*(b*x)
    simp [List.foldl, mul_left_comm, mul_comm, List.foldl_mul_assoc a (b * x) xs]

lemma extract_exp_var_i_eq_get
  {n : ℕ} (m : CPoly.CMvMonomial n) (i : Fin n) :
  extract_exp_var_i m i = Vector.get m i := by
  rfl

lemma List.foldr_mul_eq_foldl_mul
  {α : Type} [CommMonoid α] (l : List α) :
  List.foldr (fun x acc => x * acc) 1 l =
    List.foldl (fun acc x => acc * x) 1 l := by
  classical
  induction l with
  | nil =>
      simp [List.foldr, List.foldl]
  | cons a t ih =>
      simpa [List.foldr, List.foldl, ih, mul_assoc] using
        (List.foldl_mul_assoc (a := a) (b := (1 : α)) (xs := t)).symm

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

lemma Fin_foldr_loop_map
  {α β : Type} (g : α → β) :
  ∀ {n : ℕ} (f : Fin n → α) (k : ℕ) (hk : k ≤ n) (acc : List α),
    List.map g (Fin.foldr.loop n (fun x xs => f x :: xs) k hk acc) =
      Fin.foldr.loop n (fun x xs => g (f x) :: xs) k hk (List.map g acc)
| n, f, 0, hk, acc => by
    simp [Fin.foldr.loop]
| n, f, Nat.succ k, hk, acc => by
    -- unfold one step of the loop, then use IH
    simp [Fin.foldr.loop, Fin_foldr_loop_map (n := n) (f := f) (k := k) (hk := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk))]

lemma Fin_foldr_map
  {α β : Type} {n : ℕ}
  (f : Fin n → α) (g : α → β) :
  List.map g (Fin.foldr n (fun x xs => f x :: xs) [])
    =
  Fin.foldr n (fun x xs => g (f x) :: xs) [] := by
  -- expand `Fin.foldr` into `loop` and use the loop-map lemma
  simp [Fin.foldr, Fin_foldr_loop_map (g := g) (n := n) (f := f) (k := n) (hk := le_rfl) (acc := ([] : List α))]

lemma List.foldr_map'
  {α β γ : Type} (g : α → β) (h : β → γ → γ) (z : γ) :
  ∀ l : List α,
    List.foldr h z (List.map g l) = List.foldr (fun a acc => h (g a) acc) z l
| [] => by simp
| a :: l => by simp [List.foldr_map' g h z l]

lemma Fin_foldr_loop_cons
  {α : Type} {N : ℕ} (f : Fin N → α → α) :
  ∀ (k : ℕ) (hk : k ≤ N) (acc : α),
    Fin.foldr.loop N f k hk acc = Fin.foldr.loop N f k hk (by
      -- default accumulator for the “prefix” part; will be supplied by caller
      exact acc) := by
  -- dummy lemma; keep if you need later
  intro k hk acc
  rfl

lemma Fin_foldr_loop_cons_list
  (N : ℕ) :
  ∀ (k : ℕ) (hk : k ≤ N) (acc : List (Fin N)),
    Fin.foldr.loop N (fun x xs => x :: xs) k hk acc =
      Fin.foldr.loop N (fun x xs => x :: xs) k hk [] ++ acc
| 0, hk, acc => by
    simp [Fin.foldr.loop]
| Nat.succ k, hk, acc => by
    have hk' : k ≤ N := Nat.le_trans (Nat.le_succ k) hk
    have lt : k < N := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk

    have step1 :
        Fin.foldr.loop N (fun x xs => x :: xs) (Nat.succ k) hk acc
          =
        Fin.foldr.loop N (fun x xs => x :: xs) k hk' ((⟨k, lt⟩ : Fin N) :: acc) := by
      simp [Fin.foldr.loop]  -- one-step unfold

    have step2 :
        Fin.foldr.loop N (fun x xs => x :: xs) (Nat.succ k) hk []
          =
        Fin.foldr.loop N (fun x xs => x :: xs) k hk' [((⟨k, lt⟩ : Fin N))] := by
      simp [Fin.foldr.loop]  -- one-step unfold

    calc
      Fin.foldr.loop N (fun x xs => x :: xs) (Nat.succ k) hk acc
          = Fin.foldr.loop N (fun x xs => x :: xs) k hk' ((⟨k, lt⟩ : Fin N) :: acc) := step1
      _ = Fin.foldr.loop N (fun x xs => x :: xs) k hk' [] ++ ((⟨k, lt⟩ : Fin N) :: acc) := by
            simpa using (Fin_foldr_loop_cons_list N k hk' ((⟨k, lt⟩ : Fin N) :: acc))
      _ = (Fin.foldr.loop N (fun x xs => x :: xs) k hk' [] ++ [((⟨k, lt⟩ : Fin N))]) ++ acc := by
            simp [List.append_assoc]
      _ = Fin.foldr.loop N (fun x xs => x :: xs) k hk' [((⟨k, lt⟩ : Fin N))] ++ acc := by
            -- use IH backwards on the singleton accumulator
            have hsing :
                Fin.foldr.loop N (fun x xs => x :: xs) k hk' [((⟨k, lt⟩ : Fin N))]
                  =
                Fin.foldr.loop N (fun x xs => x :: xs) k hk' [] ++ [((⟨k, lt⟩ : Fin N))] := by
              simpa using (Fin_foldr_loop_cons_list N k hk' [((⟨k, lt⟩ : Fin N))])
            -- rewrite the LHS of our goal with this
            simpa [List.append_assoc] using congrArg (fun t => t ++ acc) hsing.symm
      _ = Fin.foldr.loop N (fun x xs => x :: xs) (Nat.succ k) hk [] ++ acc := by
            simp [step2]

lemma Fin_foldr_loop_castSucc_general
  {N k : ℕ} (hk : k ≤ N) :
  Fin.foldr.loop (N + 1) (fun x xs => x :: xs) k (Nat.le_trans hk (Nat.le_succ N)) [] =
    List.map Fin.castSucc (Fin.foldr.loop N (fun x xs => x :: xs) k hk []) := by
  classical
  induction k with
  | zero =>
      simp [Fin.foldr.loop]
  | succ k ih =>
      -- hk : k+1 ≤ N
      have hk' : k ≤ N := Nat.le_of_succ_le hk
      have hkL : k ≤ N + 1 := Nat.le_trans hk' (Nat.le_succ N)

      have ltN : k < N := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk
      have ltNp1 : k < N + 1 := Nat.lt_trans ltN (Nat.lt_succ_self N)

      have hcast :
          (Fin.castSucc (⟨k, ltN⟩ : Fin N)) = (⟨k, ltNp1⟩ : Fin (N+1)) := by
        simp [(Fin.castSucc_mk (n := N) (i := k) (h := ltN))]

      -- unfold one loop step on both sides
      have stepL :
          Fin.foldr.loop (N + 1) (fun x xs => x :: xs) (k + 1) (Nat.le_trans hk (Nat.le_succ N)) [] =
            Fin.foldr.loop (N + 1) (fun x xs => x :: xs) k hkL [⟨k, ltNp1⟩] := by
        simp [Fin.foldr.loop]

      have stepR :
          Fin.foldr.loop N (fun x xs => x :: xs) (k + 1) hk [] =
            Fin.foldr.loop N (fun x xs => x :: xs) k hk' [⟨k, ltN⟩] := by
        simp [Fin.foldr.loop]

      -- use your already-working cons-list lemma to move singleton acc to the end
      have hconsL :=
        (Fin_foldr_loop_cons_list (N := (N+1)) (k := k) (hk := hkL) (acc := [⟨k, ltNp1⟩]))
      have hconsR :=
        (Fin_foldr_loop_cons_list (N := N) (k := k) (hk := hk') (acc := [⟨k, ltN⟩]))

      -- rewrite and finish
      rw [stepL, stepR]
      rw [hconsL, hconsR]
      -- apply IH on the empty-loop piece
      have ih' :
          Fin.foldr.loop (N + 1) (fun x xs => x :: xs) k (Nat.le_trans hk' (Nat.le_succ N)) [] =
            List.map Fin.castSucc (Fin.foldr.loop N (fun x xs => x :: xs) k hk' []) :=
        ih (hk := hk')

      rw [ih']
      simp [List.map_append, hcast]

lemma Fin_foldr_loop_castSucc
  (n : ℕ)
  (hkL : n ≤ n + 1 + 1)
  (hkR : n ≤ n + 1) :
  Fin.foldr.loop (n + 1 + 1) (fun x xs => x :: xs) n hkL [] =
    List.map Fin.castSucc
      (Fin.foldr.loop (n + 1) (fun x xs => x :: xs) n hkR []) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (Fin_foldr_loop_castSucc_general (N := (n+1)) (k := n) hkR)

lemma List.foldl_mul_start
  {α : Type} [CommMonoid α]
  (a : α) (xs : List α) :
  a * List.foldl (fun acc x => acc * x) 1 xs
    =
  List.foldl (fun acc x => acc * x) a xs := by
  simpa using
    (List.foldl_mul_assoc (α := α) (a := a) (b := (1 : α)) (xs := xs)).symm

lemma foldl_ofFn_succ_mul_start
  {α : Type} [CommMonoid α]
  (n : ℕ) (f : Fin n.succ → α) :
  f 0 * List.foldl (fun acc x => acc * x) 1 (List.ofFn (fun i : Fin n => f i.succ))
    =
  List.foldl (fun acc x => acc * x) (f 0) (List.ofFn (fun i : Fin n => f i.succ)) := by
  simpa using List.foldl_mul_start (α := α) (a := f 0) (xs := List.ofFn (fun i : Fin n => f i.succ))

lemma Fin_foldr_loop_cons_list_values
  {α : Type} (N : ℕ) (f : Fin N → α) :
  ∀ (k : ℕ) (hk : k ≤ N) (acc : List α),
    Fin.foldr.loop N (fun i xs => f i :: xs) k hk acc
      =
    Fin.foldr.loop N (fun i xs => f i :: xs) k hk [] ++ acc
| 0, hk, acc => by
    simp [Fin.foldr.loop]
| Nat.succ k, hk, acc => by
    have hk' : k ≤ N := Nat.le_trans (Nat.le_succ k) hk
    have lt : k < N := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk
    have step :
        Fin.foldr.loop N (fun i xs => f i :: xs) (Nat.succ k) hk acc
          =
        Fin.foldr.loop N (fun i xs => f i :: xs) k hk' (f (⟨k, lt⟩ : Fin N) :: acc) := by
      simp [Fin.foldr.loop]
    have step0 :
        Fin.foldr.loop N (fun i xs => f i :: xs) (Nat.succ k) hk []
          =
        Fin.foldr.loop N (fun i xs => f i :: xs) k hk' [f (⟨k, lt⟩ : Fin N)] := by
      simp [Fin.foldr.loop]

    calc
      Fin.foldr.loop N (fun i xs => f i :: xs) (Nat.succ k) hk acc
          = Fin.foldr.loop N (fun i xs => f i :: xs) k hk' (f (⟨k, lt⟩ : Fin N) :: acc) := step
      _ = Fin.foldr.loop N (fun i xs => f i :: xs) k hk' [] ++ (f (⟨k, lt⟩ : Fin N) :: acc) := by
            simpa using (Fin_foldr_loop_cons_list_values N f k hk' (f (⟨k, lt⟩ : Fin N) :: acc))
      _ = (Fin.foldr.loop N (fun i xs => f i :: xs) k hk' [] ++ [f (⟨k, lt⟩ : Fin N)]) ++ acc := by
            simp [List.append_assoc]
      _ = Fin.foldr.loop N (fun i xs => f i :: xs) k hk' [f (⟨k, lt⟩ : Fin N)] ++ acc := by
            have hsing :
                Fin.foldr.loop N (fun i xs => f i :: xs) k hk' [f (⟨k, lt⟩ : Fin N)]
                  =
                Fin.foldr.loop N (fun i xs => f i :: xs) k hk' [] ++ [f (⟨k, lt⟩ : Fin N)] := by
              simpa using (Fin_foldr_loop_cons_list_values N f k hk' [f (⟨k, lt⟩ : Fin N)])
            simpa [List.append_assoc] using congrArg (fun t => t ++ acc) hsing.symm
      _ = Fin.foldr.loop N (fun i xs => f i :: xs) (Nat.succ k) hk [] ++ acc := by
            simp [step0]

lemma Fin_foldr_loop_values_eq_map
  {α : Type} {N : ℕ} (f : Fin N → α) (k : ℕ) (hk : k ≤ N) (acc : List (Fin N)) :
  Fin.foldr.loop N (fun i xs => f i :: xs) k hk (List.map f acc) =
    List.map f (Fin.foldr.loop N (fun i xs => i :: xs) k hk acc) := by
  simpa using
    (Fin_foldr_loop_map (g := f) (n := N) (f := fun i : Fin N => i)
      (k := k) (hk := hk) (acc := acc)).symm

lemma Fin_foldr_loop_values_eq_map_nil
  {α : Type} {N : ℕ} (f : Fin N → α) (k : ℕ) (hk : k ≤ N) :
  Fin.foldr.loop N (fun i xs => f i :: xs) k hk [] =
    List.map f (Fin.foldr.loop N (fun i xs => i :: xs) k hk []) := by
  simpa using
    (Fin_foldr_loop_values_eq_map (f := f) (k := k) (hk := hk) (acc := ([] : List (Fin N))))

lemma Finset_univ_prod_eq_foldl_ofFn
  {α : Type} [CommMonoid α] :
  ∀ (n : ℕ) (f : Fin n → α),
    (∏ x, f x) = List.foldl (fun acc x => acc * x) 1 (List.ofFn f)
| 0, f => by
    simp
| Nat.succ n, f => by
    classical
    have ih := Finset_univ_prod_eq_foldl_ofFn n (fun i : Fin n => f i.succ)
    have hprod : (∏ x : Fin (Nat.succ n), f x) = f 0 * (∏ x : Fin n, f x.succ) := by
      simpa using (Fin.prod_univ_succ (f := f))
    have hofn : List.ofFn f = f 0 :: List.ofFn (fun i : Fin n => f i.succ) := by
      simp
    calc
      (∏ x : Fin (Nat.succ n), f x)
          = f 0 * (∏ x : Fin n, f x.succ) := hprod
      _ = f 0 * List.foldl (fun acc x => acc * x) 1 (List.ofFn (fun i : Fin n => f i.succ)) := by
            simp [ih]
      _ = List.foldl (fun acc x => acc * x) 1 (List.ofFn f) := by
            rw [hofn]
            simp [List.foldl]
            simpa using
              (foldl_ofFn_succ_mul_start (α := α) (n := n) (f := f))

lemma List.ofFn_succ
  {α : Type} (n : ℕ) (f : Fin n.succ → α) :
  List.ofFn f = f 0 :: List.ofFn (fun i : Fin n => f i.succ) := by
  simp

lemma Fin_foldr_map_symm
  {α β : Type} {n : ℕ}
  (f : Fin n → α) (g : α → β) :
  Fin.foldr n (fun x xs => g (f x) :: xs) ([] : List β)
    =
  List.map g (Fin.foldr n (fun x xs => f x :: xs) ([] : List α)) := by
  simpa using (Fin_foldr_map (f := f) (g := g)).symm

@[simp] lemma CMvPolynomial_zero_val_eq_empty
  {n : ℕ} {R : Type _} [Zero R] [BEq R] [LawfulBEq R] :
  ((0 : CPoly.CMvPolynomial n R).1 : CPoly.Unlawful n R) =
    (Std.ExtTreeMap.empty : CPoly.Unlawful n R) := by
  classical
  simpa [CPoly.CMvPolynomial] using congrArg Subtype.val (CPoly.Lawful.zero_eq_empty (n := n) (R := R))

@[simp] lemma Std_ExtTreeMap_foldl_empty
  {α β σ : Type _} {cmp : α → α → Ordering} [Std.TransCmp cmp]
  (f : σ → α → β → σ) (init : σ) :
  Std.ExtTreeMap.foldl (cmp := cmp) f init (∅ : Std.ExtTreeMap α β cmp) = init := by
  simpa using (Std.ExtTreeMap.foldl_empty (cmp := cmp) (f := f) (init := init))

@[simp] lemma CMvPolynomial_eval₂_zero
  {R S : Type _} {n : ℕ} [Semiring R] [CommSemiring S]
  [BEq R] [LawfulBEq R]
  (f : R →+* S) (g : Fin n → S) :
  CPoly.CMvPolynomial.eval₂ (R := R) (S := S) (n := n) f g (0 : CPoly.CMvPolynomial n R) = 0 := by
  classical
  simp [CPoly.CMvPolynomial.eval₂, CMvPolynomial_zero_val_eq_empty]
