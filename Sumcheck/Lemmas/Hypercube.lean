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
