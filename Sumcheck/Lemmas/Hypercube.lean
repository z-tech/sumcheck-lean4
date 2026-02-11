import CompPoly.Multivariate.CMvPolynomial
import CompPoly.Multivariate.MvPolyEquiv

import Sumcheck.Src.Hypercube
import Sumcheck.Src.CMvPolynomial

-- ============================================================================
-- Lemmas moved from Src/Hypercube.lean to enforce Src = defs only
-- ============================================================================

-- Bridge lemma: Fin.cases and Fin.cons are extensionally equal
lemma Fin_cases_eq_cons {α : Type _} {n : ℕ} (a : α) (f : Fin n → α) :
    (fun i => Fin.cases a f i) = Fin.cons a f := by
  funext i
  cases i using Fin.cases with
  | zero => simp [Fin.cons]
  | succ j => simp [Fin.cons]

@[simp] lemma addCasesFun_apply {α} {m n} (f : Fin m → α) (g : Fin n → α) (i : Fin (m+n)) :
  addCasesFun f g i = Fin.addCases (m:=m) (n:=n) (motive := fun _ => α) f g i := rfl

lemma residual_sum_eq_with_openVars_def
  {𝔽 : Type} [CommRing 𝔽] [DecidableEq 𝔽]
  {k n : ℕ} (domain : List 𝔽) (ch : Fin k → 𝔽) (p : CPoly.CMvPolynomial n 𝔽) (hk : k ≤ n) :
  residual_sum (𝔽 := 𝔽) domain (k := k) (num_vars := n) ch p hk
    =
  residual_sum_with_openVars (𝔽 := 𝔽) domain (k := k) (n := n)
    (openVars := n - k) (hn := by simpa using Nat.add_sub_of_le hk) ch p := by
  classical
  unfold residual_sum residual_sum_with_openVars
  simp (config := { zeta := true })


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

-- ============================================================================
-- sum_over_hypercube_recursive lemmas (kept for backwards compat in proofs)
-- ============================================================================

@[simp] lemma sum_over_hypercube_recursive_succ
  {𝔽 β : Type _}
  (b0 b1 : 𝔽)
  (add : β → β → β)
  {m : ℕ}
  (F : (Fin (Nat.succ m) → 𝔽) → β) :
  sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add (m := Nat.succ m) F
    =
    add
      (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add (m := m)
        (fun x => F (Fin.cons b0 x)))
      (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add (m := m)
        (fun x => F (Fin.cons b1 x))) := by
  conv_lhs => unfold sum_over_hypercube_recursive
  simp only [Fin_cases_eq_cons]
  rfl

lemma sum_over_hypercube_recursive_deg_le
  {𝔽 β : Type _}
  (deg : β → ℕ) (d : ℕ)
  (b0 b1 : 𝔽)
  (add : β → β → β)
  {m : ℕ}
  (F : (Fin m → 𝔽) → β)
  (hadd : ∀ a b, deg a ≤ d → deg b ≤ d → deg (add a b) ≤ d)
  (hF : ∀ x, deg (F x) ≤ d) :
  deg (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add (m := m) F) ≤ d := by
  classical
  induction m with
  | zero =>
      -- only one assignment exists: Fin 0 → 𝔽
      simpa [sum_over_hypercube_recursive] using hF (fun i => nomatch i)
  | succ m ih =>
      -- split on the last coordinate (0 vs 1)
      have h0 :
          deg
            (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add (m := m)
              (fun x => F (Fin.cons b0 x))) ≤ d :=
        ih (F := fun x => F (Fin.cons b0 x))
           (hF := fun x => hF (Fin.cons b0 x))
      have h1 :
          deg
            (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add (m := m)
              (fun x => F (Fin.cons b1 x))) ≤ d :=
        ih (F := fun x => F (Fin.cons b1 x))
           (hF := fun x => hF (Fin.cons b1 x))
      -- now combine the two branches using hadd
      simpa [sum_over_hypercube_recursive_succ (𝔽 := 𝔽) (β := β) b0 b1 add (m := m) (F := F)]
        using hadd
          (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add (m := m) (fun x => F (Fin.cons b0 x)))
          (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add (m := m) (fun x => F (Fin.cons b1 x)))
          h0 h1

lemma sum_over_hypercube_recursive_map
  {𝔽 β γ : Type _}
  (b0 b1 : 𝔽)
  (addβ : β → β → β)
  (addγ : γ → γ → γ)
  (g : β → γ)
  (hg : ∀ a b, g (addβ a b) = addγ (g a) (g b))
  {m : ℕ}
  (F : (Fin m → 𝔽) → β) :
  g (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 addβ (m := m) F)
    =
  sum_over_hypercube_recursive (𝔽 := 𝔽) (β := γ) b0 b1 addγ (m := m) (fun x => g (F x)) := by
  classical
  induction m with
  | zero =>
      simp [sum_over_hypercube_recursive]
  | succ m ih =>
      -- Apply IH to the two branch functions explicitly
      have ih0 :
          g (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 addβ (m := m)
                (fun x => F (Fin.cons b0 x)))
            =
          sum_over_hypercube_recursive (𝔽 := 𝔽) (β := γ) b0 b1 addγ (m := m)
                (fun x => g (F (Fin.cons b0 x))) :=
        ih (F := fun x => F (Fin.cons b0 x))

      have ih1 :
          g (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 addβ (m := m)
                (fun x => F (Fin.cons b1 x)))
            =
          sum_over_hypercube_recursive (𝔽 := 𝔽) (β := γ) b0 b1 addγ (m := m)
                (fun x => g (F (Fin.cons b1 x))) :=
        ih (F := fun x => F (Fin.cons b1 x))

      -- IMPORTANT: rewrite both sides using the *succ lemma*, not the definition (avoids Nat.recAux junk)
      -- LHS becomes g (addβ (...) (...)), RHS becomes addγ (...) (...)\
      simp [sum_over_hypercube_recursive_succ, hg, ih0, ih1]

@[simp] lemma sum_over_hypercube_recursive_zero
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

lemma sum_over_hypercube_recursive_eq_of_m_eq_zero
  {𝔽 β : Type _}
  (b0 b1 : 𝔽) (add : β → β → β)
  {m : ℕ} (hm : m = 0)
  (F : (Fin m → 𝔽) → β) :
  sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β)
    (b0 := b0) (b1 := b1) (add := add) (m := m) F
    =
  F (by
    refine Eq.ndrec (motive := fun k => Fin k → 𝔽)
      (fun x : Fin 0 => nomatch x) hm.symm) := by
  subst hm
  -- goal is now reflexive
  rfl

theorem sum_over_hypercube_recursive_cast {𝔽 β : Type _}
  (b0 b1 : 𝔽)
  (add : β → β → β)
  {m m' : ℕ}
  (hm : m = m')
  (F : (Fin m → 𝔽) → β) :
  sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add (m := m) F
    =
  sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add (m := m')
    (fun x => F (x ∘ Fin.cast hm)) := by
  cases hm
  simp

theorem sum_over_hypercube_recursive_congr {𝔽 β : Type _}
  (b0 b1 : 𝔽)
  (add : β → β → β)
  {m : ℕ}
  {F G : (Fin m → 𝔽) → β}
  (hFG : ∀ x, F x = G x) :
  sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add (m := m) F
    =
  sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add (m := m) G := by
  classical
  induction m with
  | zero =>
      simp [sum_over_hypercube_recursive, hFG]
  | succ m ih =>
      simp [sum_over_hypercube_recursive, Nat.recAux, hFG]

theorem sum_over_hypercube_recursive_succ_of_hopen {𝔽 β : Type _}
  (b0 b1 : 𝔽)
  (add : β → β → β)
  {m m' : ℕ}
  (hm : m' = m + 1)
  (F : (Fin m' → 𝔽) → β) :
  sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add (m := m') F
    =
  add
    (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add (m := m)
      (fun x => F ((Fin.cons b0 x) ∘ Fin.cast hm)))
    (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add (m := m)
      (fun x => F ((Fin.cons b1 x) ∘ Fin.cast hm))) := by
  cases hm
  simp

-- ============================================================================
-- sum_over_domain_recursive lemmas
-- ============================================================================

@[simp] lemma sum_over_domain_recursive_zero
  {𝔽 β : Type _}
  (domain : List 𝔽) (add : β → β → β) (zero : β)
  (F : (Fin 0 → 𝔽) → β) :
  sum_over_domain_recursive (𝔽 := 𝔽) (β := β) domain add zero (m := 0) F
    =
  F (fun x : Fin 0 => nomatch x) := by
  simp [sum_over_domain_recursive]
  rfl

@[simp] lemma sum_over_domain_recursive_succ
  {𝔽 β : Type _}
  (domain : List 𝔽)
  (add : β → β → β) (zero : β)
  {m : ℕ}
  (F : (Fin (Nat.succ m) → 𝔽) → β) :
  sum_over_domain_recursive (𝔽 := 𝔽) (β := β) domain add zero (m := Nat.succ m) F
    =
  domain.foldl (fun acc a =>
    add acc (sum_over_domain_recursive domain add zero (m := m)
      (fun x => F (Fin.cons a x)))) zero := by
  conv_lhs => unfold sum_over_domain_recursive
  simp only [Fin_cases_eq_cons]
  rfl

lemma sum_over_domain_recursive_eq_of_m_eq_zero
  {𝔽 β : Type _}
  (domain : List 𝔽) (add : β → β → β) (zero : β)
  {m : ℕ} (hm : m = 0)
  (F : (Fin m → 𝔽) → β) :
  sum_over_domain_recursive (𝔽 := 𝔽) (β := β) domain add zero (m := m) F
    =
  F (by
    refine Eq.ndrec (motive := fun k => Fin k → 𝔽)
      (fun x : Fin 0 => nomatch x) hm.symm) := by
  subst hm
  rfl

theorem sum_over_domain_recursive_congr {𝔽 β : Type _}
  (domain : List 𝔽) (add : β → β → β) (zero : β)
  {m : ℕ}
  {F G : (Fin m → 𝔽) → β}
  (hFG : ∀ x, F x = G x) :
  sum_over_domain_recursive (𝔽 := 𝔽) (β := β) domain add zero (m := m) F
    =
  sum_over_domain_recursive (𝔽 := 𝔽) (β := β) domain add zero (m := m) G := by
  classical
  induction m with
  | zero =>
      simp [sum_over_domain_recursive, hFG]
  | succ m ih =>
      simp [sum_over_domain_recursive, Nat.recAux, hFG]

theorem sum_over_domain_recursive_cast {𝔽 β : Type _}
  (domain : List 𝔽) (add : β → β → β) (zero : β)
  {m m' : ℕ}
  (hm : m = m')
  (F : (Fin m → 𝔽) → β) :
  sum_over_domain_recursive (𝔽 := 𝔽) (β := β) domain add zero (m := m) F
    =
      sum_over_domain_recursive (𝔽 := 𝔽) (β := β) domain add zero (m := m')
    (fun x => F (x ∘ Fin.cast hm)) := by
  cases hm
  simp

-- Helper: List.foldl preserves a property if init satisfies it and f preserves it
private lemma foldl_invariant {α β : Type _}
  (P : α → Prop) (f : α → β → α) (init : α) (l : List β)
  (hinit : P init) (hstep : ∀ acc b, P acc → P (f acc b)) :
  P (List.foldl f init l) := by
  induction l generalizing init with
  | nil => simpa [List.foldl]
  | cons x xs ih =>
      simp [List.foldl]
      exact ih (f init x) (hstep init x hinit)

lemma sum_over_domain_recursive_deg_le
  {𝔽 β : Type _}
  (deg : β → ℕ) (d : ℕ)
  (domain : List 𝔽)
  (add : β → β → β) (zero : β)
  {m : ℕ}
  (F : (Fin m → 𝔽) → β)
  (hadd : ∀ a b, deg a ≤ d → deg b ≤ d → deg (add a b) ≤ d)
  (hzero : deg zero ≤ d)
  (hF : ∀ x, deg (F x) ≤ d) :
  deg (sum_over_domain_recursive (𝔽 := 𝔽) (β := β) domain add zero (m := m) F) ≤ d := by
  classical
  induction m with
  | zero =>
      simpa [sum_over_domain_recursive] using hF (fun i => nomatch i)
  | succ m ih =>
      rw [sum_over_domain_recursive_succ]
      exact foldl_invariant
        (P := fun acc => deg acc ≤ d)
        (f := fun acc a => add acc (sum_over_domain_recursive domain add zero (m := m)
          (fun x => F (Fin.cons a x))))
        (init := zero) (l := domain)
        hzero
        (fun acc a hacc => hadd acc _ hacc
          (ih (F := fun x => F (Fin.cons a x)) (hF := fun x => hF (Fin.cons a x))))

-- Helper: g commutes with foldl when g is a homomorphism
private lemma foldl_map_comm {α β γ : Type _}
  (addβ : β → α → β) (addγ : γ → α → γ)
  (g : β → γ)
  (hg : ∀ acc a, g (addβ acc a) = addγ (g acc) a)
  (init : β) (l : List α) :
  g (List.foldl addβ init l) = List.foldl addγ (g init) l := by
  induction l generalizing init with
  | nil => simp [List.foldl]
  | cons x xs ih =>
      simp only [List.foldl]
      rw [← hg]
      exact ih (addβ init x)

lemma sum_over_domain_recursive_map
  {𝔽 β γ : Type _}
  (domain : List 𝔽)
  (addβ : β → β → β) (zeroβ : β)
  (addγ : γ → γ → γ) (zeroγ : γ)
  (g : β → γ)
  (hg : ∀ a b, g (addβ a b) = addγ (g a) (g b))
  (hgz : g zeroβ = zeroγ)
  {m : ℕ}
  (F : (Fin m → 𝔽) → β) :
  g (sum_over_domain_recursive (𝔽 := 𝔽) (β := β) domain addβ zeroβ (m := m) F)
    =
  sum_over_domain_recursive (𝔽 := 𝔽) (β := γ) domain addγ zeroγ (m := m) (fun x => g (F x)) := by
  classical
  induction m with
  | zero =>
      simp [sum_over_domain_recursive]
  | succ m ih =>
      rw [sum_over_domain_recursive_succ, sum_over_domain_recursive_succ]
      -- We prove a generalized version: for any list ds, the foldl commutes with g
      -- when the inner recursive calls use the fixed `domain` (not `ds`)
      suffices hfold : ∀ (ds : List 𝔽) (accβ : β) (accγ : γ), g accβ = accγ →
        g (ds.foldl (fun acc a => addβ acc (sum_over_domain_recursive domain addβ zeroβ (m := m)
            (fun x => F (Fin.cons a x)))) accβ)
        = ds.foldl (fun acc a => addγ acc (sum_over_domain_recursive domain addγ zeroγ (m := m)
            (fun x => g (F (Fin.cons a x))))) accγ by
        exact hfold domain zeroβ zeroγ hgz
      intro ds
      induction ds with
      | nil => intro accβ accγ hacc; simpa [List.foldl]
      | cons a as iha =>
          intro accβ accγ hacc
          simp only [List.foldl]
          apply iha
          rw [hg, hacc]
          congr 1
          exact ih (F := fun x => F (Fin.cons a x))

theorem sum_over_domain_recursive_succ_of_hopen {𝔽 β : Type _}
  (domain : List 𝔽)
  (add : β → β → β) (zero : β)
  {m m' : ℕ}
  (hm : m' = m + 1)
  (F : (Fin m' → 𝔽) → β) :
  sum_over_domain_recursive (𝔽 := 𝔽) (β := β) domain add zero (m := m') F
    =
  domain.foldl (fun acc a =>
    add acc (sum_over_domain_recursive domain add zero (m := m)
      (fun x => F ((Fin.cons a x) ∘ Fin.cast hm)))) zero := by
  cases hm
  simp
