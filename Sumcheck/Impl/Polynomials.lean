import CompPoly.Lawful
import CompPoly.Unlawful
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

@[simp] def c1u {𝔽} [CommRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽] (c : 𝔽) : CPoly.Unlawful 1 𝔽 :=
  CPoly.Unlawful.C (n := 1) (R := 𝔽) c

@[simp] def x0u {𝔽} [CommRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽] :
  CPoly.Unlawful 1 𝔽 :=
by
  let zero_poly : CPoly.Unlawful 1 𝔽 := 0
  let mon_x1 : CPoly.CMvMonomial 1 := ⟨#[1], by decide⟩
  exact zero_poly.insert mon_x1 (1 : 𝔽)

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

def sum_over_boolean_extension
  {𝔽 : Type} [CommRing 𝔽] [DecidableEq 𝔽]
  {num_challenges num_vars : ℕ}
  (challenges : Fin num_challenges → 𝔽)
  (current : 𝔽)
  (p : CPoly.CMvPolynomial num_vars 𝔽)
  (hcard : num_challenges + 1 ≤ num_vars) : 𝔽 :=
by
  classical
  let fixed : Fin (num_challenges + 1) → 𝔽 := Fin.snoc challenges current
  let openVars : ℕ := num_vars - (num_challenges + 1)

  have hn : (num_challenges + 1) + openVars = num_vars := by
    simpa [openVars] using (Nat.add_sub_of_le hcard)

  -- cast the finset produced by boolean_extension to functions on Fin num_vars
  let evaluation_points : Finset (Fin num_vars → 𝔽) := by
    simpa [fixed, openVars, hn] using
      (boolean_extension (𝔽 := 𝔽) (num_fixed_vars := num_challenges + 1) fixed openVars)

  exact ∑ point ∈ evaluation_points, CPoly.CMvPolynomial.eval point p


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

def zeroP {𝔽} [CommRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽] : CPoly.CMvPolynomial 1 𝔽 :=
  c1 (𝔽 := 𝔽) 0

def oneP {𝔽} [CommRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽] : CPoly.CMvPolynomial 1 𝔽 :=
  c1 (𝔽 := 𝔽) 1

def finsetFoldl
  {α β} [DecidableEq α] [LinearOrder α]
  (s : Finset α) (init : β) (op : β → α → β) : β :=
  (s.sort (· ≤ ·)).foldl op init

def finsetSum'
  {α β} [DecidableEq α] [LinearOrder α]
  [Zero β] [Add β]
  (s : Finset α) (f : α → β) : β :=
  finsetFoldl (s := s) (init := 0) (op := fun acc a => acc + f a)

def addCasesCastPoly
  {𝔽 : Type _} [CommSemiring 𝔽]
  {k m n : ℕ}
  (hn : k + m = n)
  (left : Fin k → CPoly.CMvPolynomial 1 𝔽)
  (right : Fin m → CPoly.CMvPolynomial 1 𝔽) : Fin n → CPoly.CMvPolynomial 1 𝔽 :=
fun i =>
  Fin.addCases (m := k) (n := m) (motive := fun _ => CPoly.CMvPolynomial 1 𝔽)
    left right (Fin.cast hn.symm i)


def cubeSum01
  {𝔽 β : Type _}
  (b0 b1 : 𝔽)
  (add : β → β → β)
  {m : ℕ}
  (F : (Fin m → 𝔽) → β) : β :=
by
  classical
  induction m with
  | zero =>
      exact F (fun i => nomatch i)
  | succ m ih =>
      let extend (b : 𝔽) (x : Fin m → 𝔽) : Fin (m+1) → 𝔽 :=
        Fin.cons b x
      exact add (ih (fun x => F (extend b0 x)))
                (ih (fun x => F (extend b1 x)))

namespace CPoly

open Std

def monExp {n : ℕ} (m : CMvMonomial n) (i : Fin n) : ℕ :=
  (CMvMonomial.toFinsupp m) i

def powP {𝔽} [CommRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (p : CPoly.CMvPolynomial 1 𝔽) : ℕ → CPoly.CMvPolynomial 1 𝔽
| 0     => c1 (𝔽 := 𝔽) 1
| (e+1) => p * powP p e

def evalMonomialPoly {𝔽} [CommRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  {n : ℕ} (vs : Fin n → CPoly.CMvPolynomial 1 𝔽) (m : CPoly.CMvMonomial n) :
  CPoly.CMvPolynomial 1 𝔽 :=
(List.finRange n).foldl
  (fun acc i => acc * powP (𝔽 := 𝔽) (vs i) (CPoly.monExp m i))
  (oneP (𝔽 := 𝔽))

def eval₂Poly
  {𝔽} [CommRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  {n : ℕ}
  (f : 𝔽 → CPoly.CMvPolynomial 1 𝔽)
  (vs : Fin n → CPoly.CMvPolynomial 1 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽) : CPoly.CMvPolynomial 1 𝔽 :=
  ExtTreeMap.foldl
    (fun acc m c => (f c * evalMonomialPoly (𝔽 := 𝔽) vs m) + acc)
    (zeroP (𝔽 := 𝔽))
    p.1
