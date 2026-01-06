import CompPoly.CMvPolynomial
import Mathlib.Algebra.MvPolynomial.SchwartzZippel


import Sumcheck.Theorems.Counting.Fields
import Sumcheck.Theorems.Probability.Agreement

@[simp] noncomputable def difference_poly
  {n : ℕ} {𝔽 : Type _} [CommRing 𝔽]
  (g h : CPoly.CMvPolynomial n 𝔽) : MvPolynomial (Fin n) 𝔽 :=
  CPoly.fromCMvPolynomial g - CPoly.fromCMvPolynomial h

lemma difference_poly_eq_zero_iff
  {n : ℕ} {𝔽 : Type _} [CommRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (g h : CPoly.CMvPolynomial n 𝔽) :
  difference_poly g h = (0 : MvPolynomial (Fin n) 𝔽) ↔ g = h := by
  constructor
  · intro hd
    have hfrom :
        CPoly.fromCMvPolynomial g = CPoly.fromCMvPolynomial h := by
      exact sub_eq_zero.mp (by simpa [difference_poly] using hd)
    exact (CPoly.eq_iff_fromCMvPolynomial (u := g) (v := h)).2 hfrom
  · intro hgh
    subst hgh
    simp [difference_poly]

-- this is same as max_ind_degree when n=1
@[simp] noncomputable def total_degree_difference_poly
  {n : ℕ} {𝔽 : Type _} [CommRing 𝔽]
  (g h : CPoly.CMvPolynomial n 𝔽) : ℕ :=
  MvPolynomial.totalDegree (difference_poly g h)

@[simp] noncomputable def degree_over_field_size
  {n : ℕ} {𝔽 : Type _} [CommRing 𝔽] [Fintype 𝔽]
  (g h : CPoly.CMvPolynomial n 𝔽) : ℚ :=
  total_degree_difference_poly g h / field_size (𝔽 := 𝔽)

-- pr[ g(x) = h(x) ] ≤ deg(g - h) / |𝔽| from Schwartz-Zippel
lemma prob_agreement_le_degree_over_field_size
  {𝔽} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (g h : CPoly.CMvPolynomial 1 𝔽)
  (h_not_equal : g ≠ h) :
  prob_agreement g h h_not_equal ≤ degree_over_field_size g h :=
by
  classical
  have h_diff_non_zero : difference_poly g h ≠ (0 : MvPolynomial (Fin 1) 𝔽) := by
    intro h_assume_diff_zero
    have diff_zero_implies_eq : difference_poly g h = 0 → (g = h) := (difference_poly_eq_zero_iff g h).1
    have contra := h_not_equal (diff_zero_implies_eq h_assume_diff_zero)
    exact contra
  have sz := MvPolynomial.schwartz_zippel_totalDegree h_diff_non_zero (S := (Finset.univ : Finset 𝔽))
  simpa [CPoly.eval_equiv (p := g), CPoly.eval_equiv (p := h), sub_eq_zero] using sz
