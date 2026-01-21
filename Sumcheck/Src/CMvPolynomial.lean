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
| (e+1) => p * pow_univariate p e

def subst_monomial {n : ℕ} {𝔽} [CommRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (vs : Fin n → CPoly.CMvPolynomial 1 𝔽) (m : CPoly.CMvMonomial n) :
  CPoly.CMvPolynomial 1 𝔽 :=
(List.finRange n).foldl (fun acc i => acc * pow_univariate (vs i) (extract_exp_var_i m i)) (c1 1)

namespace CPoly

def eval₂Poly
  {n : ℕ} {𝔽} [CommRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (f : 𝔽 → CPoly.CMvPolynomial 1 𝔽)
  (vs : Fin n → CPoly.CMvPolynomial 1 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽) : CPoly.CMvPolynomial 1 𝔽 :=
Std.ExtTreeMap.foldl (fun acc m c => (f c * subst_monomial vs m) + acc) (c1 0) p.1

lemma eval₂Poly_eq_list_foldl
  {n : ℕ} {𝔽 : Type _} [CommRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (f : 𝔽 → CPoly.CMvPolynomial 1 𝔽)
  (vs : Fin n → CPoly.CMvPolynomial 1 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽) :
  CPoly.eval₂Poly (n := n) (𝔽 := 𝔽) f vs p
    =
  List.foldl
    (fun acc (mc : CPoly.CMvMonomial n × 𝔽) =>
      (f mc.2 * subst_monomial vs mc.1) + acc)
    (c1 (𝔽 := 𝔽) 0)
    p.1.toList := by
  classical
  -- this is the whole point:
  simpa [CPoly.eval₂Poly] using
    (Std.ExtTreeMap.foldl_eq_foldl_toList
      (t := p.1)
      (f := fun acc m c => (f c * subst_monomial vs m) + acc)
      (init := c1 (𝔽 := 𝔽) 0))

@[simp] lemma eval₂_add
  {n : ℕ} {R S : Type}
  [CommSemiring R] [CommSemiring S]
  [DecidableEq R] [BEq R] [LawfulBEq R]
  (f : R →+* S) (vals : Fin n → S)
  (a b : CMvPolynomial n R) :
  (a + b).eval₂ f vals = a.eval₂ f vals + b.eval₂ f vals := by
  classical
  -- move to MvPolynomial
  calc
    (a + b).eval₂ f vals
        = (fromCMvPolynomial (n := n) (R := R) (p := a + b)).eval₂ f vals := by
            simpa using (eval₂_equiv (n := n) (R := R) (S := S) (p := a + b) (f := f) (vals := vals))
    _   = (fromCMvPolynomial (n := n) (R := R) a +
            fromCMvPolynomial (n := n) (R := R) b).eval₂ f vals := by
            simp [map_add]
    _   = (fromCMvPolynomial (n := n) (R := R) a).eval₂ f vals +
          (fromCMvPolynomial (n := n) (R := R) b).eval₂ f vals := by
            -- eval₂ on MvPolynomial is a ring hom
            simpa using
              (map_add (MvPolynomial.eval₂Hom (σ := Fin n) f vals)
                (fromCMvPolynomial (n := n) (R := R) a)
                (fromCMvPolynomial (n := n) (R := R) b))
    _   = a.eval₂ f vals + b.eval₂ f vals := by
            -- move back from MvPolynomial
            simp [eval₂_equiv (n := n) (R := R) (S := S) (p := a) (f := f) (vals := vals),
                  eval₂_equiv (n := n) (R := R) (S := S) (p := b) (f := f) (vals := vals)]
