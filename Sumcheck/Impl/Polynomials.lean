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

@[simp]
def max_ind_degree
  {𝔽 : Type _} {n : ℕ} [CommSemiring 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽) : ℕ :=
  (Finset.univ : Finset (Fin n)).sup (fun i => CPoly.CMvPolynomial.degreeOf i p)

@[simp]
def ind_degree_k
  {𝔽 n} [CommSemiring 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽)
  (k : Fin n) : ℕ :=
  CPoly.CMvPolynomial.degreeOf k p
