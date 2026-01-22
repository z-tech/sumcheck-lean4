import CompPoly.CMvPolynomial
import CompPoly.MvPolyEquiv

import Sumcheck.Src.Hypercube
import Sumcheck.Src.CMvPolynomial

open scoped BigOperators

/-- Explicit (non-dependent) `Fin.cons` map we’ll use everywhere. -/
def consMap
  {𝔽 : Type _} [CommSemiring 𝔽] [DecidableEq 𝔽]
  (m : ℕ) : (𝔽 × (Fin m → 𝔽)) → (Fin (m+1) → 𝔽) :=
fun ab => Fin.cons (n := m) (α := fun _ : Fin (m+1) => 𝔽) ab.1 ab.2

lemma consMap_injective
  {𝔽 : Type _} [CommSemiring 𝔽] [DecidableEq 𝔽]
  (m : ℕ) : Function.Injective (consMap (𝔽 := 𝔽) m) := by
  intro x y hxy
  cases x with
  | mk xb xt =>
    cases y with
    | mk yb yt =>
      have h0 : xb = yb := by
        have := congrArg (fun f => f 0) hxy
        simpa [consMap] using this
      have ht : xt = yt := by
        funext i
        have := congrArg (fun f => f i.succ) hxy
        simpa [consMap] using this
      subst h0
      subst ht
      rfl

lemma addCases_injective
  {𝔽 : Type _} [CommSemiring 𝔽]
  {k m : ℕ}
  (fixed : Fin k → 𝔽) :
  Function.Injective
    (fun x : Fin m → 𝔽 =>
      (fun i : Fin (k + m) =>
        Fin.addCases
          (m := k) (n := m) (motive := fun _ => 𝔽)
          (fun i : Fin k => fixed i)
          (fun j : Fin m => x j)
          i)) := by
  intro x y hxy
  funext j
  -- evaluate both functions at a "right-side" index
  have h := congrArg (fun f => f (Fin.natAdd k j)) hxy
  -- Now reduce both sides using addCases_right
  -- (each side becomes x j and y j)
  simpa using h

lemma sum_over_hypercube_recursive_succ_def
  {𝔽 β : Type _}
  (b0 b1 : 𝔽)
  (add : β → β → β)
  (m : ℕ)
  (F : (Fin (m+1) → 𝔽) → β) :
  sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add (m := m+1) F
    =
    add
      (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add (m := m)
        (fun x => F (Fin.cons b0 x)))
      (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add (m := m)
        (fun x => F (Fin.cons b1 x))) := by
  -- This works because your definition is literally recursion on m.
  -- `simp` reduces the succ-case definitionally.
  simp [sum_over_hypercube_recursive]


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
  -- definitional reduction: your `sum_over_hypercube_recursive` is literally an `induction m`
  simp [sum_over_hypercube_recursive]

@[simp] lemma sum_over_hypercube_recursive_succ'
  {𝔽 β : Type _}
  (b0 b1 : 𝔽)
  (add : β → β → β)
  {m : ℕ}
  (F : (Fin (m+1) → 𝔽) → β) :
  sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add (m := m+1) F
    =
    add
      (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add (m := m)
        (fun x => F (Fin.cons b0 x)))
      (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add (m := m)
        (fun x => F (Fin.cons b1 x))) := by
  simp [sum_over_hypercube_recursive]

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
