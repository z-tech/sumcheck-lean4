import CompPoly.CMvPolynomial
import CompPoly.MvPolyEquiv

-- this is a constant for a polynomial w/ one variable (arity must be specified)
@[simp] def c1 {𝔽} [CommSemiring 𝔽] [BEq 𝔽] [LawfulBEq 𝔽] (c : 𝔽) :
  CPoly.CMvPolynomial 1 𝔽 :=
  CPoly.Lawful.C (n := 1) (R := 𝔽) c

-- this is the polynomial 1x^1
@[simp] def x0 {𝔽} [Field 𝔽] [DecidableEq 𝔽] :
  CPoly.CMvPolynomial 1 𝔽 := by
  classical
  let mon_x1 : CPoly.CMvMonomial 1 := ⟨#[1], by decide⟩
  let t :
      Std.ExtTreeMap (CPoly.CMvMonomial 1) 𝔽 (Ord.compare (α := CPoly.CMvMonomial 1)) :=
    (∅ : Std.ExtTreeMap (CPoly.CMvMonomial 1) 𝔽 (Ord.compare (α := CPoly.CMvMonomial 1))).insert
      mon_x1 (1 : 𝔽)

  refine ⟨(show CPoly.Unlawful 1 𝔽 from t), ?_⟩
  intro m
  -- prove: t[m]? ≠ some 0
  intro hm0

  -- if t[m]? = some 0 then (m,0) is in toList
  have hmem0 : (m, (0 : 𝔽)) ∈ t.toList := by
    exact (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some (t := t) (k := m) (v := (0 : 𝔽))).2 hm0

  -- but t has size 1, hence toList = [a]
  have hknot : mon_x1 ∉ (∅ : Std.ExtTreeMap (CPoly.CMvMonomial 1) 𝔽 (Ord.compare (α := CPoly.CMvMonomial 1))) := by
    simp
  have hsize : t.size = 1 := by
    simpa [t, hknot] using
      (Std.ExtTreeMap.size_insert
        (t := (∅ : Std.ExtTreeMap (CPoly.CMvMonomial 1) 𝔽 (Ord.compare (α := CPoly.CMvMonomial 1))))
        (k := mon_x1) (v := (1 : 𝔽)))
  have hlen : t.toList.length = 1 := by
    simp [Std.ExtTreeMap.length_toList, hsize]
  rcases (List.length_eq_one_iff.mp hlen) with ⟨a, ha⟩

  -- and (mon_x1,1) is in the toList (because lookup at mon_x1 is some 1)
  have hget1 : t[mon_x1]? = some (1 : 𝔽) := by
    simpa [t] using
      (Std.ExtTreeMap.getElem?_insert_self
        (t := (∅ : Std.ExtTreeMap (CPoly.CMvMonomial 1) 𝔽 (Ord.compare (α := CPoly.CMvMonomial 1))))
        (k := mon_x1) (v := (1 : 𝔽)))
  have hmem1 : (mon_x1, (1 : 𝔽)) ∈ t.toList := by
    exact (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some (t := t) (k := mon_x1) (v := (1 : 𝔽))).2 hget1

  -- since toList = [a], both (m,0) and (mon_x1,1) must equal a
  have ha0 : (m, (0 : 𝔽)) = a := by
    have : (m, (0 : 𝔽)) ∈ [a] := by simpa [ha] using hmem0
    simpa using (List.mem_singleton.1 this)
  have ha1 : (mon_x1, (1 : 𝔽)) = a := by
    have : (mon_x1, (1 : 𝔽)) ∈ [a] := by simpa [ha] using hmem1
    simpa using (List.mem_singleton.1 this)

  -- compare second components: 0 = 1, contradiction
  have : (0 : 𝔽) = (1 : 𝔽) := by
    have := congrArg Prod.snd (ha0.trans ha1.symm)
    simpa using this
  exact one_ne_zero (this.symm)

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
