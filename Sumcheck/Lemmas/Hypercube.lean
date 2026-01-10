import CompPoly.CMvPolynomial

import Sumcheck.Impl.Hypercube
import Sumcheck.Impl.Polynomials

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

lemma hypercube_succ_eq_image
  {𝔽 : Type _} [CommSemiring 𝔽] [DecidableEq 𝔽]
  (m : ℕ) :
  hypercube_n (𝔽 := 𝔽) (m+1)
    =
    (({0, 1} : Finset 𝔽).product (hypercube_n (𝔽 := 𝔽) m)).image
      (consMap (𝔽 := 𝔽) m) := by
  classical
  ext f
  constructor
  · intro hf
    -- unfold membership using mem_piFinset, *without simp loops*
    have hf' :
        f ∈ Fintype.piFinset (fun _ : Fin (m+1) => ({0, 1} : Finset 𝔽)) := by
      -- just change definitional unfolding of hypercube_n
      simpa [hypercube_n] using hf
    have hmem : ∀ j : Fin (m+1), f j ∈ ({0, 1} : Finset 𝔽) :=
      (Fintype.mem_piFinset).1 hf'

    refine Finset.mem_image.2 ?_
    refine ⟨(f 0, Fin.tail f), ?_, ?_⟩
    · -- (f0, tail f) ∈ {0,1} × hypercube_n m
      refine Finset.mem_product.2 ?_
      refine ⟨hmem 0, ?_⟩
      -- show tail f ∈ hypercube_n m
      have ht' :
          Fin.tail f ∈ Fintype.piFinset (fun _ : Fin m => ({0, 1} : Finset 𝔽)) := by
        refine (Fintype.mem_piFinset).2 ?_
        intro a
        -- tail f a = f a.succ
        simpa [Fin.tail] using (hmem a.succ)
      -- convert back to hypercube_n
      simpa [hypercube_n] using ht'
    · -- consMap (f0, tail f) = f
      funext j
      refine Fin.cases (by simp [consMap]) (fun j' => ?_) j
      simp [consMap, Fin.tail]

  · intro hf
    rcases Finset.mem_image.1 hf with ⟨ab, hab, rfl⟩
    have hb : ab.1 ∈ ({0, 1} : Finset 𝔽) := (Finset.mem_product.1 hab).1
    have ht : ab.2 ∈ hypercube_n (𝔽 := 𝔽) m := (Finset.mem_product.1 hab).2

    -- show consMap ab ∈ hypercube_n (m+1)
    have ht' :
        ab.2 ∈ Fintype.piFinset (fun _ : Fin m => ({0, 1} : Finset 𝔽)) := by
      simpa [hypercube_n] using ht
    have htmem : ∀ a : Fin m, ab.2 a ∈ ({0, 1} : Finset 𝔽) :=
      (Fintype.mem_piFinset).1 ht'

    -- now build membership in piFinset for m+1
    have hcons' :
        (consMap (𝔽 := 𝔽) m ab)
          ∈ Fintype.piFinset (fun _ : Fin (m+1) => ({0, 1} : Finset 𝔽)) := by
      refine (Fintype.mem_piFinset).2 ?_
      intro j
      refine Fin.cases (by simpa [consMap] using hb) (fun j' => ?_) j
      -- succ case
      simpa [consMap] using htmem j'
    simpa [hypercube_n] using hcons'

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

lemma sum_hypercube_succ
  {𝔽 : Type _} [CommSemiring 𝔽] [DecidableEq 𝔽]
  {β : Type _} [AddCommMonoid β]
  (m : ℕ) (F : (Fin (m + 1) → 𝔽) → β) :
  (hypercube_n (𝔽 := 𝔽) (m+1)).sum F
    =
    (({0, 1} : Finset 𝔽).product (hypercube_n (𝔽 := 𝔽) m)).sum
      (fun ab => F (consMap (𝔽 := 𝔽) m ab)) := by
  classical
  let S : Finset (𝔽 × (Fin m → 𝔽)) :=
    ({0, 1} : Finset 𝔽).product (hypercube_n (𝔽 := 𝔽) m)
  let g := consMap (𝔽 := 𝔽) m

  have hImg : hypercube_n (𝔽 := 𝔽) (m+1) = S.image g := by
    -- NO simp: just unfold S/g and use the lemma
    unfold S g
    exact hypercube_succ_eq_image (𝔽 := 𝔽) m

  rw [hImg]

  have hinj : Set.InjOn g (↑S) := by
    intro x hx y hy hxy
    exact consMap_injective (𝔽 := 𝔽) m hxy

  -- your Finset.sum_image:
  -- InjOn g s → ∑ x ∈ image g s, f x = ∑ x ∈ s, f (g x)
  have hsum : (∑ x ∈ S.image g, F x) = ∑ ab ∈ S, F (g ab) :=
    Finset.sum_image (f := F) (s := S) (g := g) hinj

  -- convert binder sums to `.sum`
  simpa [Finset.sum, S, g] using hsum

def addCasesCast
  {𝔽 : Type _} [CommSemiring 𝔽]
  {k m n : ℕ}
  (hn : k + m = n)
  (fixed : Fin k → 𝔽)
  (x : Fin m → 𝔽) : Fin n → 𝔽 :=
fun i => Fin.addCases (m := k) (n := m) (motive := fun _ => 𝔽)
  fixed x (Fin.cast hn.symm i)


lemma sum_over_boolean_extension_succ
  {𝔽 : Type _} [CommRing 𝔽] [DecidableEq 𝔽]
  {num_vars k : ℕ}
  (ch : Fin k → 𝔽)
  (a : 𝔽)
  (p : CPoly.CMvPolynomial num_vars 𝔽)
  (h1 : k + 1 ≤ num_vars)
  (h2 : k + 2 ≤ num_vars) :
  (@sum_over_boolean_extension 𝔽 _ _ k num_vars ch a p h1)
    =
    (@sum_over_boolean_extension 𝔽 _ _ (k+1) num_vars (Fin.snoc ch a) (0 : 𝔽) p h2)
    +
    (@sum_over_boolean_extension 𝔽 _ _ (k+1) num_vars (Fin.snoc ch a) (1 : 𝔽) p h2) := by
  -- proof goes here
  sorry
