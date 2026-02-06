import CompPoly.CMvPolynomial
import CompPoly.MvPolyEquiv

import Sumcheck.Src.Hypercube
import Sumcheck.Src.CMvPolynomial

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
      -- LHS becomes g (addβ (...) (...)), RHS becomes addγ (...) (...)
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
