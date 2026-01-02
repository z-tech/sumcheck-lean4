import CompPoly.Lawful
import CompPoly.CMvMonomial
import CompPoly.CMvPolynomial
import Mathlib.Data.ZMod.Basic

import Sumcheck.Hypercube

@[simp] def x0 {𝔽 : Type _} [CommRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽] :
  CPoly.CMvPolynomial 1 𝔽 :=
by
  let zero_poly : CPoly.Unlawful 1 𝔽 := 0
  let mon_x1 : CPoly.CMvMonomial 1 := ⟨#[1], by decide⟩ -- x^1
  let coeff : 𝔽 := 1
  -- insert the monomial with coeff 1 into the zero polynomial
  -- convert from raw (unlawful) to checked (lawful) format
  exact CPoly.Lawful.fromUnlawful (zero_poly.insert mon_x1 coeff)

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
      (boolean_extension fixed (num_vars - (num_challenges + 1)))
  let sum := evaluation_points.sum fun point => CPoly.CMvPolynomial.eval point p
  sum

-- compute a univariate polynomial going through the given points
@[simp] def lagrange_interpolation_n_points
  {𝔽} [Field 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  -- TODO: points should probs be list of pairs so we can do like {(0, v), (1, v), (ω, v), (ω^2, v), (ω^3, v), etc ...}
  (points : Fin num_points → 𝔽) : CPoly.CMvPolynomial 1 𝔽 :=
by
  classical
  let X : CPoly.CMvPolynomial 1 𝔽 := x0 (𝔽 := 𝔽)

  -- constant embedding
  let C1 : 𝔽 → CPoly.CMvPolynomial 1 𝔽 :=
    fun a => CPoly.Lawful.C (n := 1) (R := 𝔽) a

  let idxs : List (Fin num_points) := List.finRange num_points

  -- Lagrange term for a fixed i
  let term : Fin num_points → CPoly.CMvPolynomial 1 𝔽 :=
    fun i =>
      C1 (points i) *
        (idxs.foldl
          (fun acc j =>
            if h : j = i then
              acc
            else
              acc *
                (X - C1 ((j : ℕ) : 𝔽)) *
                C1 ((((i : ℕ) : 𝔽) - ((j : ℕ) : 𝔽))⁻¹))
          1)

  -- sum the terms
  exact idxs.foldl (fun acc i => acc + term i) 0
