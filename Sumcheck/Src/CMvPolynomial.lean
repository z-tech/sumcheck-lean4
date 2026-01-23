import CompPoly.CMvPolynomial
import CompPoly.MvPolyEquiv

-- this is a constant for a polynomial w/ one variable (arity must be specified)
@[simp] def c1 {𝔽} [CommRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽] c :=
  CPoly.Lawful.C (n := 1) (R := 𝔽) c

-- this is the polynomial 1x^1
@[simp] def x0 {𝔽} [CommRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽] :
  CPoly.CMvPolynomial 1 𝔽 :=
by
  let mon_x1 : CPoly.CMvMonomial 1 := ⟨#[1], by decide⟩
  exact CPoly.Lawful.fromUnlawful (n := 1) (R := 𝔽) <|
    CPoly.Unlawful.ofList [(mon_x1, (1 : 𝔽))]

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

lemma ind_degree_k_le_max_ind_degree
  {𝔽 : Type _} {n : ℕ} [CommSemiring 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽) (k : Fin n) :
  ind_degree_k (𝔽 := 𝔽) (n := n) p k ≤ max_ind_degree (𝔽 := 𝔽) (n := n) p := by
  classical
  simp [ind_degree_k, max_ind_degree]
  exact
    Finset.le_sup
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => CPoly.CMvPolynomial.degreeOf i p)
      (by simp)

def extract_exp_var_i {n : ℕ} (m : CPoly.CMvMonomial n) (i : Fin n) : ℕ :=
  (CPoly.CMvMonomial.toFinsupp m) i

def pow_univariate {𝔽} [CommRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (p : CPoly.CMvPolynomial 1 𝔽) : ℕ → CPoly.CMvPolynomial 1 𝔽
| 0     => c1 1
| (e+1) => Mul.mul p (pow_univariate p e)

def subst_monomial {n : ℕ} {𝔽} [CommRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (vs : Fin n → CPoly.CMvPolynomial 1 𝔽) (m : CPoly.CMvMonomial n) :
  CPoly.CMvPolynomial 1 𝔽 :=
(List.finRange n).foldl
  (fun acc i => Mul.mul acc (pow_univariate (vs i) (extract_exp_var_i m i)))
  (c1 1)

namespace CPoly

def eval₂Poly
  {n : ℕ} {𝔽} [CommRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (f : 𝔽 → CPoly.CMvPolynomial 1 𝔽)
  (vs : Fin n → CPoly.CMvPolynomial 1 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽) : CPoly.CMvPolynomial 1 𝔽 :=
Std.ExtTreeMap.foldl (fun acc m c => (f c * subst_monomial vs m) + acc) (c1 0) p.1
