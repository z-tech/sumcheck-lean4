import CompPoly.CMvPolynomial
import Mathlib.Data.ZMod.Basic

import Sumcheck.Hypercube

@[simp] def boolean_extension {𝔽 : Type _} [CommRing 𝔽] [DecidableEq 𝔽]
  {num_fixed_vars : ℕ}
  (fixed : Fin num_fixed_vars → 𝔽)
  (num_open_vars : ℕ) : Finset (Fin (num_fixed_vars + num_open_vars) → 𝔽) :=
by
  classical
  let hypercube : Finset (Fin num_open_vars → 𝔽) :=
    hypercube_n (𝔽 := 𝔽) num_open_vars
  exact hypercube.image (fun x => Fin.addCases fixed x)

@[simp] def sum_over_boolean_extension {𝔽} [CommRing 𝔽] [DecidableEq 𝔽]
  (challenges : Fin num_challenges → 𝔽)
  (current : 𝔽)
  (p : CPoly.CMvPolynomial num_vars 𝔽)
  (hcard : num_challenges + 1 <= num_vars) : 𝔽 :=
  let fixed : Fin (num_challenges + 1) → 𝔽 := Fin.snoc challenges current
  let evaluation_points : Finset (Fin num_vars → 𝔽) := by
    have hn :
        num_challenges + 1 + (num_vars - (num_challenges + 1)) = num_vars :=
      Nat.add_sub_of_le hcard
    simpa [hn] using
      (boolean_extension (fixed := fixed) (num_open_vars := num_vars - (num_challenges + 1)))
  let sum := evaluation_points.sum fun point => CPoly.CMvPolynomial.eval point p
  sum
