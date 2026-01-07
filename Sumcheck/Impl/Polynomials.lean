import CompPoly.Lawful
import CompPoly.CMvMonomial
import CompPoly.CMvPolynomial
import Mathlib.Data.ZMod.Basic

import Sumcheck.Impl.Hypercube

-- this is a constant for a polynomial w/ one variable (arity must be specified)
@[simp] def c1 {𝔽} [CommRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽] c :=
  CPoly.Lawful.C (n := 1) (R := 𝔽) c

-- this is the polynomial 1x^1
@[simp] def x0 {𝔽} [CommRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽] :
  CPoly.CMvPolynomial 1 𝔽 :=
by
  -- empty poly
  let zero_poly : CPoly.Unlawful 1 𝔽 := 0
  -- mon x^1 ... monomials can't have coeffs btw that's why we need this def
  let mon_x1 : CPoly.CMvMonomial 1 := ⟨#[1], by decide⟩
  let coeff : 𝔽 := 1
  -- insert the monomial using coeff 1 into the zero polynomial
  let raw := zero_poly.insert mon_x1 coeff
  -- convert from raw (unlawful) to checked (lawful) format
  exact CPoly.Lawful.fromUnlawful raw

-- -- loop through all variables and return the highest degree d
-- @[simp] def max_ind_degree {𝔽} [Field 𝔽] (f : CPoly.CMvPolynomial n 𝔽) : ℕ :=
--   (Finset.univ : Finset (Fin n)).sup (fun i => CPoly.CMvPolynomial.degreeOf i f)

-- takes fixed vars set and returns set containing all extensions over cube size open_vars
@[simp] def boolean_extension {𝔽 : Type _} [CommRing 𝔽] [DecidableEq 𝔽]
  {num_fixed_vars : ℕ}
  (fixed : Fin num_fixed_vars → 𝔽)
  (num_open_vars : ℕ) : Finset (Fin (num_fixed_vars + num_open_vars) → 𝔽) :=
by
  classical
  let hypercube : Finset (Fin num_open_vars → 𝔽) :=
    hypercube_n (𝔽 := 𝔽) num_open_vars
  exact hypercube.image (fun x => Fin.addCases fixed x)

-- takes challenges and current assignment and computes sum over cube size num_vars
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

-- computes a univariate polynomial passing through the given points
-- TODO: points should probs instead be list of pairs so we can do like {(0, v), (1, v), (ω, v), (ω^2, v), (ω^3, v), etc ...}
@[simp] def lagrange_interpolation_n_points
  {𝔽} [Field 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (y_vals : Fin num_points → 𝔽) : CPoly.CMvPolynomial 1 𝔽 :=
by
  classical
  let x_vals : List (Fin num_points) := List.finRange num_points
  let terms : Fin num_points → CPoly.CMvPolynomial 1 𝔽 :=
    fun term_idx =>
      c1 (y_vals term_idx) *
        (x_vals.foldl
          (fun acc j =>
            if h : j = term_idx then
              acc
            else
              acc *
                (x0 - c1 (j : 𝔽)) *
                c1 (((term_idx : 𝔽) - j)⁻¹))
          1)
  exact x_vals.foldl (fun acc term_idx => acc + terms term_idx) 0
