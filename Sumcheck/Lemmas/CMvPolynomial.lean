import CompPoly.CMvPolynomial
import CompPoly.MvPolyEquiv
import Mathlib.Data.Finsupp.Notation

import Sumcheck.Src.CMvPolynomial
import Sumcheck.Lemmas.ExtTreeMap

@[simp] lemma CMvPolynomial_zero_val_eq_empty
  {n : ℕ} {R : Type _} [Zero R] [BEq R] [LawfulBEq R] :
  ((0 : CPoly.CMvPolynomial n R).1 : CPoly.Unlawful n R) =
    (Std.ExtTreeMap.empty : CPoly.Unlawful n R) := by
  classical
  simpa [CPoly.CMvPolynomial] using congrArg Subtype.val (CPoly.Lawful.zero_eq_empty (n := n) (R := R))

@[simp] lemma CMvPolynomial_eval₂_zero
  {R S : Type _} {n : ℕ} [Semiring R] [CommSemiring S]
  [BEq R] [LawfulBEq R]
  (f : R →+* S) (g : Fin n → S) :
  CPoly.CMvPolynomial.eval₂ (R := R) (S := S) (n := n) f g (0 : CPoly.CMvPolynomial n R) = 0 := by
  classical
  simp [CPoly.CMvPolynomial.eval₂, CMvPolynomial_zero_val_eq_empty]

lemma fromCMvPolynomial_c1_eq_C {𝔽 : Type _} [CommSemiring 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
(c : 𝔽) :
  CPoly.fromCMvPolynomial (R := 𝔽) (c1 (𝔽 := 𝔽) c)
    = (MvPolynomial.C c : MvPolynomial (Fin 1) 𝔽) := by
  classical
  ext m
  simp [CPoly.coeff_eq, c1, MvPolynomial.coeff_C, CPoly.Lawful.C, CPoly.CMvPolynomial.coeff,
    CPoly.Unlawful.C]
  by_cases hc : c = 0
  · simp [hc]
    change
      ((∅ : Std.ExtTreeMap (CPoly.CMvMonomial 1) 𝔽 (Ord.compare (α := CPoly.CMvMonomial 1)))[
          CPoly.CMvMonomial.ofFinsupp m]?).getD 0 = 0
    simp
  · simp [hc]
    have hz : ((CPoly.CMvMonomial.zero : CPoly.CMvMonomial 1)).toFinsupp = (0 : Fin 1 →₀ ℕ) := by
      ext
      simp [CPoly.CMvMonomial.toFinsupp, CPoly.CMvMonomial.zero]
    by_cases hm : (0 : Fin 1 →₀ ℕ) = m
    · subst hm
      have hmono0 :
          CPoly.CMvMonomial.ofFinsupp (0 : Fin 1 →₀ ℕ) = (CPoly.CMvMonomial.zero : CPoly.CMvMonomial 1) := by
        apply CPoly.CMvMonomial.injective_toFinsupp
        simp [hz]
      change
        ((
            (∅ : Std.ExtTreeMap (CPoly.CMvMonomial 1) 𝔽 (Ord.compare (α := CPoly.CMvMonomial 1))).insert
              (CPoly.CMvMonomial.zero : CPoly.CMvMonomial 1) c)[
            CPoly.CMvMonomial.ofFinsupp (0 : Fin 1 →₀ ℕ)]?).getD 0 = c
      rw [hmono0]
      simp
    · simp [hm]
      have hneq :
          CPoly.CMvMonomial.ofFinsupp m ≠ (CPoly.CMvMonomial.zero : CPoly.CMvMonomial 1) := by
        intro h
        apply hm
        have ht := congrArg (fun t => CPoly.CMvMonomial.toFinsupp t) h
        have hm0 : m = (0 : Fin 1 →₀ ℕ) := by
          simpa [hz] using ht
        exact hm0.symm
      haveI : Std.LawfulBEqOrd (CPoly.CMvMonomial 1) := by
        infer_instance
      haveI : LawfulBEq (CPoly.CMvMonomial 1) := by
        infer_instance
      have hcmp :
          compare (CPoly.CMvMonomial.zero : CPoly.CMvMonomial 1) (CPoly.CMvMonomial.ofFinsupp m) ≠ Ordering.eq := by
        intro h
        have hiff :
            compare (CPoly.CMvMonomial.zero : CPoly.CMvMonomial 1) (CPoly.CMvMonomial.ofFinsupp m) = Ordering.eq ↔
              ((CPoly.CMvMonomial.zero : CPoly.CMvMonomial 1) == CPoly.CMvMonomial.ofFinsupp m) := by
          simp
        have hbeq : ((CPoly.CMvMonomial.zero : CPoly.CMvMonomial 1) == CPoly.CMvMonomial.ofFinsupp m) :=
          hiff.1 h
        have hne' : (CPoly.CMvMonomial.zero : CPoly.CMvMonomial 1) ≠ CPoly.CMvMonomial.ofFinsupp m :=
          fun hEq => hneq hEq.symm
        exact (not_beq_of_ne hne') hbeq
      change
        ((
            (∅ : Std.ExtTreeMap (CPoly.CMvMonomial 1) 𝔽 (Ord.compare (α := CPoly.CMvMonomial 1))).insert
              (CPoly.CMvMonomial.zero : CPoly.CMvMonomial 1) c)[
            CPoly.CMvMonomial.ofFinsupp m]?).getD 0 = 0
      have hins :
          ((
              (∅ : Std.ExtTreeMap (CPoly.CMvMonomial 1) 𝔽 (Ord.compare (α := CPoly.CMvMonomial 1))).insert
                (CPoly.CMvMonomial.zero : CPoly.CMvMonomial 1) c)[
              CPoly.CMvMonomial.ofFinsupp m]?) =
            if compare (CPoly.CMvMonomial.zero : CPoly.CMvMonomial 1) (CPoly.CMvMonomial.ofFinsupp m) = Ordering.eq then
              some c
            else
              (∅ : Std.ExtTreeMap (CPoly.CMvMonomial 1) 𝔽 (Ord.compare (α := CPoly.CMvMonomial 1)))[
                CPoly.CMvMonomial.ofFinsupp m]? := by
        simpa using
          (Std.ExtTreeMap.getElem?_insert
            (t := (∅ : Std.ExtTreeMap (CPoly.CMvMonomial 1) 𝔽 (Ord.compare (α := CPoly.CMvMonomial 1))))
            (k := (CPoly.CMvMonomial.zero : CPoly.CMvMonomial 1)) (v := c) :
            ((
                (∅ : Std.ExtTreeMap (CPoly.CMvMonomial 1) 𝔽 (Ord.compare (α := CPoly.CMvMonomial 1))).insert
                  (CPoly.CMvMonomial.zero : CPoly.CMvMonomial 1) c)[
                CPoly.CMvMonomial.ofFinsupp m]?) =
              if compare (CPoly.CMvMonomial.zero : CPoly.CMvMonomial 1) (CPoly.CMvMonomial.ofFinsupp m) = Ordering.eq then
                some c
              else
                (∅ : Std.ExtTreeMap (CPoly.CMvMonomial 1) 𝔽 (Ord.compare (α := CPoly.CMvMonomial 1)))[
                  CPoly.CMvMonomial.ofFinsupp m]?)
      have hinsD := congrArg (fun o : Option 𝔽 => o.getD 0) hins
      simp [hcmp]

lemma fromCMvPolynomial_x0_eq_X {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽] :
  CPoly.fromCMvPolynomial (R := 𝔽) (x0 (𝔽 := 𝔽)) = (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) 𝔽) := by
  classical
  ext s
  simp [CPoly.coeff_eq, x0, CPoly.CMvPolynomial.coeff, MvPolynomial.coeff_X']
  set mon_x1 : CPoly.CMvMonomial 1 := { toArray := #[1], size_toArray := x0._proof_1 }
  have hmon_toF : CPoly.CMvMonomial.toFinsupp mon_x1 = (Finsupp.single (0 : Fin 1) 1) := by
    refine Finsupp.ext ?_
    intro i
    fin_cases i
    simp [CPoly.CMvMonomial.toFinsupp, mon_x1]
  have hmon : mon_x1 = CPoly.CMvMonomial.ofFinsupp (Finsupp.single (0 : Fin 1) 1) := by
    apply (CPoly.CMvMonomial.injective_toFinsupp (n := 1))
    simp [hmon_toF]
  let t : Std.ExtTreeMap (CPoly.CMvMonomial 1) 𝔽 (Ord.compare (α := CPoly.CMvMonomial 1)) :=
    (∅ : Std.ExtTreeMap (CPoly.CMvMonomial 1) 𝔽 (Ord.compare (α := CPoly.CMvMonomial 1))).insert
      mon_x1 (1 : 𝔽)
  change t[CPoly.CMvMonomial.ofFinsupp s]?.getD 0 = if (fun₀ | 0 => 1) = s then 1 else 0
  by_cases h : CPoly.CMvMonomial.ofFinsupp s = mon_x1
  · have hs : (Finsupp.single (0 : Fin 1) 1) = s := by
      apply (CPoly.CMvMonomial.injective_ofFinsupp (n := 1))
      calc
        CPoly.CMvMonomial.ofFinsupp (Finsupp.single (0 : Fin 1) 1)
            = mon_x1 := by simp [hmon]
        _ = CPoly.CMvMonomial.ofFinsupp s := by simpa using h.symm
    have hlookup : t[CPoly.CMvMonomial.ofFinsupp s]? = some (1 : 𝔽) := by
      simp [t, h]
    simp [hlookup, hs]
  · have hs : (Finsupp.single (0 : Fin 1) 1) ≠ s := by
      intro hs
      apply h
      have : CPoly.CMvMonomial.ofFinsupp s = CPoly.CMvMonomial.ofFinsupp (Finsupp.single (0 : Fin 1) 1) := by
        simp [hs]
      exact this.trans hmon.symm
    have hne : mon_x1 ≠ CPoly.CMvMonomial.ofFinsupp s := by
      intro h'
      apply h
      simpa using h'.symm
    have hlookup : t[CPoly.CMvMonomial.ofFinsupp s]? = none := by
      -- unfold the insert-lookup formula and simplify
      simp [t, Std.compare_eq_iff_eq, hne]
    simp [hlookup, hs]

-- ============================================================================
-- Lemmas moved from Src/CMvPolynomial.lean to enforce Src = defs only
-- ============================================================================

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
