import CompPoly.Multivariate.FinSuccEquiv
import CompPoly.Multivariate.CMvPolynomialEvalLemmas
import CompPoly.Multivariate.Rename
import Sumcheck.Src.CMvPolynomial
import Sumcheck.Properties.Lemmas.Hypercube
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Logic.Equiv.Basic

/-!
# Specialization and linearization (R-operator) on `CMvPolynomial`

Two generic polynomial operators used by Shamir's TQBF arithmetization but
applicable anywhere a multilinear extension is needed (GKR, Reed-Muller codes,
multi-party protocols). Defined here in the `CPoly.CMvPolynomial` namespace so
that migration to CompPoly upstream is a rename-free move.

## Definitions

* `specialize0 p c` — substitute the field element `c` for variable 0 in
  `p : CMvPolynomial (n+1) 𝔽`, yielding a polynomial in the remaining
  `n` variables.
* `linearize0 p` — the **R-operator** (Shamir) applied at variable 0:
  produces `(1 - X₀) · p[X₀ := 0] + X₀ · p[X₀ := 1]`. Key property: agrees
  with `p` at boolean points (`X₀ ∈ {0, 1}`) while having individual degree
  in `X₀` at most 1. Iterated over all variables, this produces the
  multilinear extension.

## What's here

* Definitions: `specialize0`, `linearize0`, `linearize_i`, `linearizeAll`.
* Evaluation at boolean points:
  - `eval_specialize0 : (specialize0 p c).eval x = p.eval (Fin.cons c x)`
  - `eval_linearize0_boolean`, `eval_linearize_i_boolean`,
    `eval_linearizeAll_boolean` — agreement with the original at boolean
    inputs (the defining property of the multilinear extension).
* Degree bounds:
  - `degreeOf_linearize0_zero_le_one`, `degreeOf_linearize_i_le_one` — the
    linearized variable has degree ≤ 1.
  - `degreeOf_specialize0_succ_le`, `degreeOf_linearize0_succ_le`,
    `degreeOf_linearize_i_ne_le` — non-increasing at other variables.
  - **`degreeOf_linearizeAll_le_one`** — full multilinearity of the output.
* Generic bridge: `MvPolynomial.degreeOf_succ_le_of_coeffs_le` — upper-bound
  a polynomial's individual degree at `j.succ` from bounds on the coefficients
  of its `finSuccEquiv`-decomposition.

## TODO

* Propose upstreaming these operators to `CompPoly/Multilinear/`.
-/

namespace CPoly.CMvPolynomial

variable {𝔽 : Type} [Field 𝔽] [BEq 𝔽] [LawfulBEq 𝔽] {n : ℕ}

/-- Substitute variable 0 with the field element `c`, returning a polynomial
in the remaining `n` variables. -/
noncomputable def specialize0 (p : CMvPolynomial (n + 1) 𝔽) (c : 𝔽) :
    CMvPolynomial n 𝔽 :=
  (CMvPolynomial.finSuccEquiv p).eval (CMvPolynomial.C c)

/-- The **R-operator** (linearization) at variable 0: `linearize0 p` agrees
with `p` at `X₀ = 0` and `X₀ = 1`, and is linear in `X₀`. Explicitly,
`linearize0 p = (1 - X₀) · p[X₀ := 0] + X₀ · p[X₀ := 1]`, constructed inside
`Polynomial (CMvPolynomial n 𝔽)` and lifted back via `finSuccEquiv.symm`. -/
noncomputable def linearize0 (p : CMvPolynomial (n + 1) 𝔽) :
    CMvPolynomial (n + 1) 𝔽 :=
  CMvPolynomial.finSuccEquiv.symm
    ((1 - Polynomial.X) * Polynomial.C (specialize0 p 0) +
      Polynomial.X * Polynomial.C (specialize0 p 1))

/-- Bridge: `CMvPolynomial.finSuccEquiv`, mapped through `fromCMvPolynomial`
(viewed as a RingHom via `polyRingEquiv`), equals Mathlib's
`MvPolynomial.finSuccEquiv` applied to `fromCMvPolynomial p`. This is the
coherence required to transport evaluation identities between the two
representations. -/
private lemma map_fromCMvPolynomial_finSuccEquiv
    (p : CMvPolynomial (n + 1) 𝔽) :
    Polynomial.map (polyRingEquiv (n := n) (R := 𝔽)).toRingHom
        (CMvPolynomial.finSuccEquiv p) =
      MvPolynomial.finSuccEquiv 𝔽 n (fromCMvPolynomial p) := by
  show Polynomial.map (polyRingEquiv (n := n) (R := 𝔽)).toRingHom
      (polynomialCMvPolyEquiv.symm
        ((MvPolynomial.finSuccEquiv 𝔽 n) (polyRingEquiv p))) = _
  -- `polynomialCMvPolyEquiv = Polynomial.mapEquiv polyRingEquiv`, whose forward
  -- action equals `Polynomial.map polyRingEquiv.toRingHom` definitionally; the
  -- equiv's round-trip then closes the goal.
  change polynomialCMvPolyEquiv
      (polynomialCMvPolyEquiv.symm
        ((MvPolynomial.finSuccEquiv 𝔽 n) (polyRingEquiv p))) = _
  rw [polynomialCMvPolyEquiv.apply_symm_apply]
  rfl

/-- Bridge: `fromCMvPolynomial ∘ specialize0` corresponds exactly to
Mathlib's `finSuccEquiv` followed by `Polynomial.eval` at a constant. -/
theorem fromCMvPolynomial_specialize0 (p : CMvPolynomial (n + 1) 𝔽) (c : 𝔽) :
    fromCMvPolynomial (specialize0 p c) =
      (MvPolynomial.finSuccEquiv 𝔽 n (fromCMvPolynomial p)).eval
        (MvPolynomial.C c) := by
  unfold specialize0
  rw [show fromCMvPolynomial
          ((CMvPolynomial.finSuccEquiv p).eval (CMvPolynomial.C c))
        = ((CMvPolynomial.finSuccEquiv p).map
            (polyRingEquiv (n := n) (R := 𝔽)).toRingHom).eval
            ((polyRingEquiv (n := n) (R := 𝔽)).toRingHom (CMvPolynomial.C c))
      from (Polynomial.eval_map_apply
        (polyRingEquiv (n := n) (R := 𝔽)).toRingHom _).symm]
  rw [map_fromCMvPolynomial_finSuccEquiv]
  rw [show (polyRingEquiv (n := n) (R := 𝔽)).toRingHom (CMvPolynomial.C c)
        = (MvPolynomial.C c : MvPolynomial (Fin n) 𝔽)
      from CMvPolynomial.fromCMvPolynomial_C c]

omit [BEq 𝔽] [LawfulBEq 𝔽] in
/-- Bridge: on `MvPolynomial`, evaluating `finSuccEquiv` at `C c` equals the
algebra homomorphism sending `X 0 ↦ C c` and `X j.succ ↦ X j`. -/
private lemma finSuccEquiv_eval_C_eq_aeval (c : 𝔽)
    (f : MvPolynomial (Fin (n + 1)) 𝔽) :
    (MvPolynomial.finSuccEquiv 𝔽 n f).eval (MvPolynomial.C c)
      = MvPolynomial.aeval
          (Fin.cons (MvPolynomial.C c : MvPolynomial (Fin n) 𝔽)
            (fun j : Fin n => MvPolynomial.X j)) f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    simp [MvPolynomial.finSuccEquiv_apply]
  | add p q hp hq =>
    rw [_root_.map_add, Polynomial.eval_add, _root_.map_add, hp, hq]
  | mul_X p i hp =>
    rw [_root_.map_mul, Polynomial.eval_mul, _root_.map_mul, hp]
    congr 1
    induction i using Fin.cases with
    | zero =>
      rw [MvPolynomial.finSuccEquiv_X_zero, Polynomial.eval_X,
          MvPolynomial.aeval_X, Fin.cons_zero]
    | succ j =>
      rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.eval_C,
          MvPolynomial.aeval_X, Fin.cons_succ]

/-- **Specialization commutes with a 0↔1 swap.** Swapping variables 0 and 1
before two nested `specialize0` calls (with respective constants `b, c`) yields
the same polynomial as doing the two specializations in the opposite order
(`c, b`) without the swap. -/
theorem specialize0_commute (p : CMvPolynomial (n + 2) 𝔽) (b c : 𝔽) :
    specialize0 (specialize0
        (CMvPolynomial.rename (Equiv.swap (0 : Fin (n + 2)) 1) p) b) c
      = specialize0 (specialize0 p c) b := by
  apply CPoly.fromCMvPolynomial_injective
  rw [fromCMvPolynomial_specialize0, fromCMvPolynomial_specialize0,
      CPoly.fromCMvPolynomial_rename,
      fromCMvPolynomial_specialize0, fromCMvPolynomial_specialize0,
      finSuccEquiv_eval_C_eq_aeval, finSuccEquiv_eval_C_eq_aeval,
      finSuccEquiv_eval_C_eq_aeval, finSuccEquiv_eval_C_eq_aeval,
      MvPolynomial.aeval_rename,
      MvPolynomial.comp_aeval_apply, MvPolynomial.comp_aeval_apply]
  congr 1
  apply congrArg
  funext i
  induction i using Fin.cases with
  | zero =>
    -- swap 0 = 1; cons (C b) X 1 = X 0; aeval _ (X 0) = C c.
    -- cons (C c) X 0 = C c; aeval _ (C c) = C c.
    have h1 : (Fin.cons (MvPolynomial.C b : MvPolynomial (Fin (n + 1)) 𝔽)
        (fun j : Fin (n + 1) =>
          (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) 𝔽))
        : Fin (n + 2) → MvPolynomial (Fin (n + 1)) 𝔽) (1 : Fin (n + 2))
        = (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) 𝔽) := by
      change (Fin.cons _ _ (Fin.succ (0 : Fin (n + 1)))) = _
      rw [Fin.cons_succ]
    simp only [Function.comp_apply, Equiv.swap_apply_left, h1, Fin.cons_zero,
               MvPolynomial.aeval_X, MvPolynomial.aeval_C,
               MvPolynomial.algebraMap_eq]
  | succ j =>
    induction j using Fin.cases with
    | zero =>
      -- swap 1 = 0; cons (C b) X 0 = C b; aeval _ (C b) = C b.
      -- cons (C c) X 1 = X 0; aeval _ (X 0) = C b.
      have h1 : (Fin.cons (MvPolynomial.C c : MvPolynomial (Fin (n + 1)) 𝔽)
          (fun j : Fin (n + 1) =>
            (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) 𝔽))
          : Fin (n + 2) → MvPolynomial (Fin (n + 1)) 𝔽) (1 : Fin (n + 2))
          = (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) 𝔽) := by
        change (Fin.cons _ _ (Fin.succ (0 : Fin (n + 1)))) = _
        rw [Fin.cons_succ]
      have hsw : Equiv.swap (0 : Fin (n + 2)) 1 (Fin.succ 0) = 0 := by
        change Equiv.swap (0 : Fin (n + 2)) 1 (1 : Fin (n + 2)) = 0
        exact Equiv.swap_apply_right _ _
      simp only [Function.comp_apply, Fin.cons_succ, hsw, Fin.cons_zero,
                 MvPolynomial.aeval_X, MvPolynomial.aeval_C,
                 MvPolynomial.algebraMap_eq]
    | succ k =>
      have h0 : (Fin.succ (Fin.succ k) : Fin (n + 2)) ≠ 0 := Fin.succ_ne_zero _
      have h1 : (Fin.succ (Fin.succ k) : Fin (n + 2)) ≠ 1 := by
        intro h
        have hk : Fin.succ k = (0 : Fin (n + 1)) :=
          Fin.succ_injective _ h
        exact Fin.succ_ne_zero k hk
      simp only [Function.comp_apply, Fin.cons_succ,
                 Equiv.swap_apply_of_ne_of_ne h0 h1,
                 MvPolynomial.aeval_X]

/-- **Specialization evaluates correctly.** Evaluating `specialize0 p c` at a
point `x : Fin n → 𝔽` equals evaluating `p` at the extended point
`Fin.cons c x`. -/
theorem eval_specialize0 (p : CMvPolynomial (n + 1) 𝔽) (c : 𝔽)
    (x : Fin n → 𝔽) :
    (specialize0 p c).eval x = p.eval (Fin.cons c x) := by
  rw [CPoly.eval_equiv, CPoly.eval_equiv (p := p)]
  unfold specialize0
  -- Push `fromCMvPolynomial` through `Polynomial.eval` via `eval_map_apply`:
  -- fromCMvPolynomial (q.eval r) = (q.map fromCMvPolynomial).eval (fromCMvPolynomial r)
  rw [show fromCMvPolynomial
          ((CMvPolynomial.finSuccEquiv p).eval (CMvPolynomial.C c))
        = ((CMvPolynomial.finSuccEquiv p).map
            (polyRingEquiv (n := n) (R := 𝔽)).toRingHom).eval
            ((polyRingEquiv (n := n) (R := 𝔽)).toRingHom (CMvPolynomial.C c))
      from (Polynomial.eval_map_apply
        (polyRingEquiv (n := n) (R := 𝔽)).toRingHom _).symm]
  rw [map_fromCMvPolynomial_finSuccEquiv]
  have hC :
      (polyRingEquiv (n := n) (R := 𝔽)).toRingHom (CMvPolynomial.C c)
        = (MvPolynomial.C c : MvPolynomial (Fin n) 𝔽) :=
    CMvPolynomial.fromCMvPolynomial_C c
  rw [hC, MvPolynomial.eval_polynomial_eval_finSuccEquiv]
  rw [show (fun i => Fin.cases (MvPolynomial.eval x (MvPolynomial.C c)) x i)
        = Fin.cons c x by simp [MvPolynomial.eval_C, Fin_cases_eq_cons]]

/-- **R-operator boolean agreement.** At any point whose variable-0 value is
boolean (0 or 1 in the field), `linearize0 p` agrees with `p`. This is the
defining property of the linear extension. -/
theorem eval_linearize0_boolean (p : CMvPolynomial (n + 1) 𝔽)
    (x : Fin (n + 1) → 𝔽) (h : x 0 = 0 ∨ x 0 = 1) :
    (linearize0 p).eval x = p.eval x := by
  have hx : x = Fin.cons (x 0) (Fin.tail x) := (Fin.cons_self_tail x).symm
  conv_lhs => rw [hx]
  conv_rhs => rw [hx]
  rw [← eval_specialize0, ← eval_specialize0]
  -- Compute specialize0 (linearize0 p) c = (1 - C c) · specialize0 p 0 + C c · specialize0 p 1.
  have hsp : specialize0 (linearize0 p) (x 0)
      = (1 - CMvPolynomial.C (x 0)) * specialize0 p 0
        + CMvPolynomial.C (x 0) * specialize0 p 1 := by
    show (CMvPolynomial.finSuccEquiv (linearize0 p)).eval
        (CMvPolynomial.C (x 0)) = _
    unfold linearize0
    rw [CMvPolynomial.finSuccEquiv.apply_symm_apply]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
  rw [hsp]
  simp only [CPoly.eval_add, CPoly.eval_mul, CPoly.eval_sub,
             CPoly.eval_one, CPoly.eval_C]
  rw [eval_specialize0, eval_specialize0, eval_specialize0]
  rcases h with h0 | h1
  · rw [h0]; ring
  · rw [h1]; ring

/-! ### Generalization to arbitrary variable index -/

/-- Evaluating a renamed polynomial at a point equals evaluating the original
polynomial at the precomposed point. -/
theorem eval_rename_c {m k : ℕ} (f : Fin m → Fin k) (p : CMvPolynomial m 𝔽)
    (x : Fin k → 𝔽) :
    (CMvPolynomial.rename f p).eval x = p.eval (x ∘ f) := by
  rw [CPoly.eval_equiv, CPoly.eval_equiv (p := p)]
  rw [CPoly.fromCMvPolynomial_rename]
  exact _root_.MvPolynomial.eval_rename (k := f) x (fromCMvPolynomial p)

/-- Linearize at an arbitrary variable index `i`: rename to move `i` into
position 0, apply `linearize0`, rename back. Because `Equiv.swap 0 i` is
self-inverse, the inner and outer renames are the same function. -/
noncomputable def linearize_i {n : ℕ} (i : Fin (n + 1))
    (p : CMvPolynomial (n + 1) 𝔽) : CMvPolynomial (n + 1) 𝔽 :=
  CMvPolynomial.rename (Equiv.swap (0 : Fin (n + 1)) i)
    (linearize0 (CMvPolynomial.rename (Equiv.swap (0 : Fin (n + 1)) i) p))

/-- **R-operator boolean agreement at arbitrary index.** At any point whose
`i`-th coordinate is boolean (0 or 1 in the field), `linearize_i i p` agrees
with `p`. -/
theorem eval_linearize_i_boolean {n : ℕ} (i : Fin (n + 1))
    (p : CMvPolynomial (n + 1) 𝔽) (x : Fin (n + 1) → 𝔽)
    (h : x i = 0 ∨ x i = 1) :
    (linearize_i i p).eval x = p.eval x := by
  unfold linearize_i
  rw [eval_rename_c, eval_linearize0_boolean, eval_rename_c]
  · -- p.eval (x ∘ swap ∘ swap) = p.eval x : swap is self-inverse.
    congr 1
    funext j
    simp [Equiv.swap_apply_def]
    by_cases hj₀ : j = 0
    · subst hj₀; by_cases hi : i = 0 <;> simp [hi]
    · by_cases hji : j = i <;> simp [hj₀, hji]
  · -- (x ∘ swap) 0 = x i, which is boolean by `h`.
    show x (Equiv.swap (0 : Fin (n + 1)) i 0) = 0 ∨
         x (Equiv.swap (0 : Fin (n + 1)) i 0) = 1
    rw [Equiv.swap_apply_left]
    exact h

/-! ### Degree bounds -/

/-- Bridge: the `natDegree` of a `CMvPolynomial` after `finSuccEquiv` equals the
individual degree of its 0-th variable. The CompPoly analog of Mathlib's
`MvPolynomial.natDegree_finSuccEquiv`. -/
private theorem natDegree_finSuccEquiv_c (p : CMvPolynomial (n + 1) 𝔽) :
    (CMvPolynomial.finSuccEquiv p).natDegree = p.degreeOf 0 := by
  have hinj : Function.Injective
      (polyRingEquiv (n := n) (R := 𝔽)).toRingHom :=
    polyRingEquiv.injective
  rw [← Polynomial.natDegree_map_eq_of_injective hinj
        (CMvPolynomial.finSuccEquiv p),
      map_fromCMvPolynomial_finSuccEquiv,
      MvPolynomial.natDegree_finSuccEquiv]
  exact (congrFun (CPoly.degreeOf_equiv (S := 𝔽) (p := p)) 0).symm

/-- **R-operator linearizes variable 0.** After `linearize0`, the individual
degree in variable 0 is at most 1. -/
theorem degreeOf_linearize0_zero_le_one (p : CMvPolynomial (n + 1) 𝔽) :
    (linearize0 p).degreeOf 0 ≤ 1 := by
  rw [← natDegree_finSuccEquiv_c]
  unfold linearize0
  rw [CMvPolynomial.finSuccEquiv.apply_symm_apply]
  -- Bound natDegree of (1 - X) * C a + X * C b.
  have h1 : Polynomial.natDegree
      ((1 - Polynomial.X) * Polynomial.C (specialize0 p 0) :
        Polynomial (CMvPolynomial n 𝔽)) ≤ 1 := by
    refine le_trans Polynomial.natDegree_mul_le ?_
    have h1X : Polynomial.natDegree
        ((1 - Polynomial.X) : Polynomial (CMvPolynomial n 𝔽)) ≤ 1 := by
      refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
      rw [Polynomial.natDegree_one]
      exact max_le (Nat.zero_le _) Polynomial.natDegree_X_le
    have hC : Polynomial.natDegree
        (Polynomial.C (specialize0 p 0) : Polynomial (CMvPolynomial n 𝔽)) = 0 :=
      Polynomial.natDegree_C _
    omega
  have h2 : Polynomial.natDegree
      (Polynomial.X * Polynomial.C (specialize0 p 1) :
        Polynomial (CMvPolynomial n 𝔽)) ≤ 1 := by
    refine le_trans Polynomial.natDegree_mul_le ?_
    rw [Polynomial.natDegree_C]
    exact Nat.add_le_add Polynomial.natDegree_X_le (le_refl 0)
  exact le_trans (Polynomial.natDegree_add_le _ _) (max_le h1 h2)

/-- Bridge: renaming preserves individual degree at the image index when the
rename function is injective. The CompPoly analog of Mathlib's
`MvPolynomial.degreeOf_rename_of_injective`. -/
private theorem degreeOf_rename_of_injective_c {m k : ℕ}
    {f : Fin m → Fin k} (h : Function.Injective f)
    (i : Fin m) (p : CMvPolynomial m 𝔽) :
    (CMvPolynomial.rename f p).degreeOf (f i) = p.degreeOf i := by
  rw [congrFun (CPoly.degreeOf_equiv (S := 𝔽) (p := CMvPolynomial.rename f p))
        (f i),
      congrFun (CPoly.degreeOf_equiv (S := 𝔽) (p := p)) i,
      CPoly.fromCMvPolynomial_rename,
      MvPolynomial.degreeOf_rename_of_injective h i]

/-- Generic bridge: if every coefficient of a `finSuccEquiv`-decomposition has
individual degree at most `d` in variable `j`, the original polynomial has
individual degree at most `d` in `j.succ`. This is the reverse direction of
Mathlib's `MvPolynomial.degreeOf_coeff_finSuccEquiv`. -/
private theorem MvPolynomial.degreeOf_succ_le_of_coeffs_le
    {n d : ℕ} {R : Type*} [CommSemiring R]
    {A : MvPolynomial (Fin (n + 1)) R} (j : Fin n)
    (h : ∀ i, ((MvPolynomial.finSuccEquiv R n A).coeff i).degreeOf j ≤ d) :
    A.degreeOf j.succ ≤ d := by
  rw [MvPolynomial.degreeOf_eq_sup]
  refine Finset.sup_le ?_
  intro m hm
  have hmem : Finsupp.tail m ∈
      ((MvPolynomial.finSuccEquiv R n A).coeff (m 0)).support := by
    rw [MvPolynomial.mem_support_coeff_finSuccEquiv, Finsupp.cons_tail]
    exact hm
  have hle := MvPolynomial.monomial_le_degreeOf j hmem
  rw [Finsupp.tail_apply] at hle
  exact le_trans hle (h (m 0))

/-- Specialization does not increase other variables' individual degrees:
`(specialize0 p c).degreeOf j ≤ p.degreeOf j.succ`. Equivalently, evaluating
variable 0 at a constant can only remove variable 0 without growing any
remaining variable's degree. -/
theorem degreeOf_specialize0_succ_le (p : CMvPolynomial (n + 1) 𝔽) (c : 𝔽)
    (j : Fin n) :
    (specialize0 p c).degreeOf j ≤ p.degreeOf j.succ := by
  -- Bridge to MvPolynomial land, then bound through
  -- `MvPolynomial.degreeOf_coeff_finSuccEquiv` per term of the eval-as-sum.
  rw [congrFun (CPoly.degreeOf_equiv (S := 𝔽) (p := specialize0 p c)) j,
      congrFun (CPoly.degreeOf_equiv (S := 𝔽) (p := p)) j.succ]
  unfold specialize0
  rw [show fromCMvPolynomial
        ((CMvPolynomial.finSuccEquiv p).eval (CMvPolynomial.C c))
      = ((CMvPolynomial.finSuccEquiv p).map
          (polyRingEquiv (n := n) (R := 𝔽)).toRingHom).eval
          ((polyRingEquiv (n := n) (R := 𝔽)).toRingHom (CMvPolynomial.C c))
      from (Polynomial.eval_map_apply
        (polyRingEquiv (n := n) (R := 𝔽)).toRingHom _).symm]
  rw [map_fromCMvPolynomial_finSuccEquiv]
  have hC :
      (polyRingEquiv (n := n) (R := 𝔽)).toRingHom (CMvPolynomial.C c)
        = (MvPolynomial.C c : MvPolynomial (Fin n) 𝔽) :=
    CMvPolynomial.fromCMvPolynomial_C c
  rw [hC]
  -- Now: degreeOf j ((finSuccEquiv (fromCMvPolynomial p)).eval (C c))
  --      ≤ degreeOf j.succ (fromCMvPolynomial p)
  set A := fromCMvPolynomial p
  set q := MvPolynomial.finSuccEquiv 𝔽 n A
  rw [Polynomial.eval_eq_sum_range]
  refine le_trans (MvPolynomial.degreeOf_sum_le j _ _) ?_
  refine Finset.sup_le ?_
  intro i _
  -- degreeOf j (q.coeff i * (C c)^i) ≤ degreeOf j (q.coeff i) + 0 ≤ A.degreeOf j.succ.
  refine le_trans (MvPolynomial.degreeOf_mul_le _ _ _) ?_
  have hpow : (MvPolynomial.C c : MvPolynomial (Fin n) 𝔽) ^ i
      = MvPolynomial.C (c ^ i) := by
    rw [← map_pow]
  rw [hpow, MvPolynomial.degreeOf_C, Nat.add_zero]
  exact MvPolynomial.degreeOf_coeff_finSuccEquiv A j i

/-- **R-operator is non-increasing at other variables.** `linearize0` does not
grow the individual degree at any variable other than 0. -/
theorem degreeOf_linearize0_succ_le (p : CMvPolynomial (n + 1) 𝔽) (j : Fin n) :
    (linearize0 p).degreeOf j.succ ≤ p.degreeOf j.succ := by
  rw [congrFun (CPoly.degreeOf_equiv (S := 𝔽) (p := linearize0 p)) j.succ,
      congrFun (CPoly.degreeOf_equiv (S := 𝔽) (p := p)) j.succ]
  refine MvPolynomial.degreeOf_succ_le_of_coeffs_le j ?_
  intro i
  rw [← map_fromCMvPolynomial_finSuccEquiv, Polynomial.coeff_map]
  unfold linearize0
  rw [CMvPolynomial.finSuccEquiv.apply_symm_apply]
  have hsp0 : (fromCMvPolynomial (specialize0 p 0)).degreeOf j
      ≤ (fromCMvPolynomial p).degreeOf j.succ := by
    rw [← congrFun (CPoly.degreeOf_equiv (S := 𝔽) (p := specialize0 p 0)) j,
        ← congrFun (CPoly.degreeOf_equiv (S := 𝔽) (p := p)) j.succ]
    exact degreeOf_specialize0_succ_le p 0 j
  have hsp1 : (fromCMvPolynomial (specialize0 p 1)).degreeOf j
      ≤ (fromCMvPolynomial p).degreeOf j.succ := by
    rw [← congrFun (CPoly.degreeOf_equiv (S := 𝔽) (p := specialize0 p 1)) j,
        ← congrFun (CPoly.degreeOf_equiv (S := 𝔽) (p := p)) j.succ]
    exact degreeOf_specialize0_succ_le p 1 j
  -- Compute coeff i of (1 - X) * C a_0 + X * C a_1 by cases on i.
  rcases i with _ | _ | i
  · -- i = 0: coeff = a_0
    simp only [Polynomial.coeff_add, sub_mul, one_mul, Polynomial.coeff_sub,
               Polynomial.coeff_X_mul_zero, Polynomial.coeff_C_zero,
               sub_zero, add_zero]
    exact hsp0
  · -- i = 1: coeff = a_1 - a_0
    simp only [Polynomial.coeff_add, sub_mul, one_mul, Polynomial.coeff_sub,
               Polynomial.coeff_X_mul, Polynomial.coeff_C_zero,
               Polynomial.coeff_C_ne_zero (show (1 : ℕ) ≠ 0 by decide),
               zero_sub, neg_add_eq_sub]
    rw [_root_.map_sub]
    exact le_trans (MvPolynomial.degreeOf_sub_le _ _ _) (max_le hsp1 hsp0)
  · -- i = k + 2: coeff = 0
    simp only [Polynomial.coeff_add, sub_mul, one_mul, Polynomial.coeff_sub,
               Polynomial.coeff_X_mul,
               Polynomial.coeff_C_ne_zero (show (i + 1 : ℕ) ≠ 0 by omega),
               Polynomial.coeff_C_ne_zero (show (i + 2 : ℕ) ≠ 0 by omega),
               sub_zero, add_zero]
    simp [MvPolynomial.degreeOf_zero]

/-- Non-increasing of `linearize0` extended to all non-zero indices. -/
private theorem degreeOf_linearize0_ne_zero_le {n : ℕ}
    (k : Fin (n + 1)) (hk : k ≠ 0) (p : CMvPolynomial (n + 1) 𝔽) :
    (linearize0 p).degreeOf k ≤ p.degreeOf k := by
  induction k using Fin.cases with
  | zero => exact absurd rfl hk
  | succ k' => exact degreeOf_linearize0_succ_le p k'

/-- **R-operator at arbitrary index linearizes that index.** After
`linearize_i i`, the individual degree in variable `i` is at most 1. -/
theorem degreeOf_linearize_i_le_one {n : ℕ} (i : Fin (n + 1))
    (p : CMvPolynomial (n + 1) 𝔽) :
    (linearize_i i p).degreeOf i ≤ 1 := by
  unfold linearize_i
  have hrename := degreeOf_rename_of_injective_c
    (f := (Equiv.swap (0 : Fin (n + 1)) i : Fin (n + 1) → Fin (n + 1)))
    (Equiv.injective _) 0
    (linearize0 (CMvPolynomial.rename (Equiv.swap 0 i) p))
  rw [Equiv.swap_apply_left] at hrename
  rw [hrename]
  exact degreeOf_linearize0_zero_le_one _

/-- **R-operator is non-increasing at other variables.** At any variable
other than the linearization target, `linearize_i i` does not grow the
individual degree. -/
theorem degreeOf_linearize_i_ne_le {n : ℕ} (i : Fin (n + 1))
    (p : CMvPolynomial (n + 1) 𝔽) (j : Fin (n + 1)) (hji : j ≠ i) :
    (linearize_i i p).degreeOf j ≤ p.degreeOf j := by
  unfold linearize_i
  have hσj : Equiv.swap (0 : Fin (n + 1)) i j ≠ 0 := by
    intro h
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at h
    exact hji h
  have step1 := degreeOf_rename_of_injective_c
    (f := (Equiv.swap (0 : Fin (n + 1)) i : Fin (n + 1) → Fin (n + 1)))
    (Equiv.injective _)
    (Equiv.swap (0 : Fin (n + 1)) i j)
    (linearize0 (CMvPolynomial.rename (Equiv.swap 0 i) p))
  rw [Equiv.swap_apply_self] at step1
  rw [step1]
  refine le_trans (degreeOf_linearize0_ne_zero_le _ hσj _) ?_
  have step2 := degreeOf_rename_of_injective_c
    (f := (Equiv.swap (0 : Fin (n + 1)) i : Fin (n + 1) → Fin (n + 1)))
    (Equiv.injective _) j p
  exact le_of_eq step2

/-! ### Full multilinearization -/

/-- `linearizeAll p` linearizes `p` in every variable, yielding a polynomial
whose individual degree in each variable is at most 1 (multilinear). At
boolean-cube points it agrees with `p`, making it the multilinear extension
of `p|_{0,1}^n`. -/
noncomputable def linearizeAll : ∀ {n : ℕ}, CMvPolynomial n 𝔽 → CMvPolynomial n 𝔽
  | 0, p => p
  | _ + 1, p => (List.finRange _).foldl (fun q i => linearize_i i q) p

/-- Helper: iterating `linearize_i` over any list of indices preserves
evaluation at boolean-cube points. -/
private lemma eval_foldl_linearize_i_boolean {m : ℕ}
    (l : List (Fin (m + 1)))
    (p : CMvPolynomial (m + 1) 𝔽)
    (x : Fin (m + 1) → 𝔽) (hx : ∀ i, x i = 0 ∨ x i = 1) :
    (l.foldl (fun q i => linearize_i i q) p).eval x = p.eval x := by
  induction l generalizing p with
  | nil => rfl
  | cons i tail ih =>
    rw [List.foldl_cons, ih]
    exact eval_linearize_i_boolean i p x (hx i)

/-- **Multilinearization boolean agreement.** `linearizeAll` agrees with the
original polynomial at every boolean-cube point — this is the defining
property of the multilinear extension. -/
theorem eval_linearizeAll_boolean : ∀ {n : ℕ} (p : CMvPolynomial n 𝔽)
    (x : Fin n → 𝔽), (∀ i, x i = 0 ∨ x i = 1) →
    (linearizeAll p).eval x = p.eval x
  | 0, _, _, _ => rfl
  | _ + 1, p, x, hx => eval_foldl_linearize_i_boolean _ p x hx

/-- Helper: `linearize_i` preserves the "degree ≤ 1" bound at any variable. -/
private lemma degreeOf_linearize_i_preserve_le_one {m : ℕ} (i : Fin (m + 1))
    (p : CMvPolynomial (m + 1) 𝔽) (k : Fin (m + 1)) (hk : p.degreeOf k ≤ 1) :
    (linearize_i i p).degreeOf k ≤ 1 := by
  by_cases h : k = i
  · subst h; exact degreeOf_linearize_i_le_one k p
  · exact le_trans (degreeOf_linearize_i_ne_le i p k h) hk

/-- Helper: iterating `linearize_i` preserves degree ≤ 1 for any variable. -/
private lemma degreeOf_foldl_linearize_i_preserve_le_one {m : ℕ}
    (l : List (Fin (m + 1)))
    (p : CMvPolynomial (m + 1) 𝔽)
    (k : Fin (m + 1)) (hk : p.degreeOf k ≤ 1) :
    (l.foldl (fun q i => linearize_i i q) p).degreeOf k ≤ 1 := by
  induction l generalizing p with
  | nil => exact hk
  | cons hd tail ih =>
    rw [List.foldl_cons]
    exact ih _ (degreeOf_linearize_i_preserve_le_one hd p k hk)

/-- Helper: for any index appearing in the fold list, the final polynomial has
degree ≤ 1 at that index. -/
private lemma degreeOf_foldl_linearize_i_mem_le_one {m : ℕ}
    (l : List (Fin (m + 1)))
    (p : CMvPolynomial (m + 1) 𝔽)
    (k : Fin (m + 1)) (hk : k ∈ l) :
    (l.foldl (fun q i => linearize_i i q) p).degreeOf k ≤ 1 := by
  induction l generalizing p with
  | nil => exact absurd hk (List.not_mem_nil)
  | cons hd tail ih =>
    rw [List.foldl_cons]
    rw [List.mem_cons] at hk
    rcases hk with hkhd | hktail
    · subst hkhd
      exact degreeOf_foldl_linearize_i_preserve_le_one tail _ k
        (degreeOf_linearize_i_le_one k p)
    · exact ih _ hktail

/-- **Full multilinearity.** `linearizeAll p` has individual degree at most
`1` in every variable. -/
theorem degreeOf_linearizeAll_le_one : ∀ {n : ℕ} (p : CMvPolynomial n 𝔽)
    (j : Fin n), (linearizeAll p).degreeOf j ≤ 1
  | 0, _, j => j.elim0
  | _ + 1, p, j => by
    show ((List.finRange _).foldl (fun q i => linearize_i i q) p).degreeOf j ≤ 1
    exact degreeOf_foldl_linearize_i_mem_le_one _ p j (List.mem_finRange j)

end CPoly.CMvPolynomial
