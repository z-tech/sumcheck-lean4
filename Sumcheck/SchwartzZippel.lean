import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open Polynomial Finset

variable {R : Type*} [Field R] [DecidableEq R]

/-- Number of roots on domain S -/
def num_roots_over_domain (P : Polynomial R) (S : Finset R) : ℕ :=
  (S.filter (λ x => P.eval x = 0)).card

lemma num_roots_over_domain_le_natDegree
    (S : Finset R) :
    ∀ {P : Polynomial R}, P ≠ 0 →
      num_roots_over_domain P S ≤ P.natDegree := by
  classical
  refine Finset.induction_on S ?base ?step
  · -- base
    intro P hP
    simp [num_roots_over_domain]
  · -- step
    intro a S ha IH P hP
    by_cases hPa : P.eval a = 0
    · -- a is a root: P = (X - C a) * Q
      obtain ⟨Q, hPQ⟩ : ∃ Q, P = (X - C a) * Q :=
        (X_sub_C_dvd_iff.mpr hPa)
      have hQne : Q ≠ 0 := by
        intro hQ
        have : P = 0 := by simpa [hPQ, hQ]
        exact hP this
      -- roots of P in S ⊆ roots of Q in S (since a ∉ S)
      have hsubset :
          (S.filter fun x => P.eval x = 0) ⊆ (S.filter fun x => Q.eval x = 0) := by
        intro x hx
        rcases Finset.mem_filter.mp hx with ⟨hxS, hx0⟩
        have hxne : x ≠ a := by
          intro hxa; exact ha (hxa ▸ hxS)
        have hmul : (x - a) * Q.eval x = 0 := by
          -- eval P at x and use P = (X - C a) * Q
          simpa [hPQ, eval_mul, eval_sub, eval_X, eval_C, hx0]
        have hQx : Q.eval x = 0 := by
          rcases mul_eq_zero.mp hmul with hxa0 | hq0
          · exact (hxne (sub_eq_zero.mp hxa0)).elim
          · exact hq0
        exact Finset.mem_filter.mpr ⟨hxS, hQx⟩
      have hcard_le :
          num_roots_over_domain P S ≤ num_roots_over_domain Q S :=
        Finset.card_le_of_subset hsubset
      -- insert a: contributes +1 because hPa and a ∉ S
      have hinsert :
          num_roots_over_domain P (insert a S)
            = 1 + num_roots_over_domain P S := by
        simp [num_roots_over_domain, Finset.filter_insert, hPa, ha]
      -- degrees: natDegree P = natDegree Q + 1
      have hdeg : P.natDegree = Q.natDegree + 1 := by
        have := natDegree_mul (by simpa using (X_sub_C_ne (a := a))) hQne
        simpa [hPQ, natDegree_X_sub_C, add_comm] using this
      -- conclude
      calc
        num_roots_over_domain P (insert a S)
            = 1 + num_roots_over_domain P S := hinsert
        _ ≤ 1 + num_roots_over_domain Q S :=
            Nat.add_le_add_left hcard_le 1
        _ ≤ 1 + Q.natDegree :=
            Nat.add_le_add_left (IH hQne) 1
        _ = P.natDegree := by
            simpa [hdeg, add_comm]
    · -- a is not a root: count unchanged
      have : num_roots_over_domain P (insert a S)
            = num_roots_over_domain P S := by
        simp [num_roots_over_domain, Finset.filter_insert, hPa, ha]
      simpa [this] using IH hP

/-- Univariate Schwartz–Zippel over a field:
the fraction of points in `S` at which `P` vanishes is at most `deg(P)/|S|`. -/
theorem schwartz_zippel_univariate
  (P : Polynomial R) (S : Finset R) (hp : P ≠ 0) (hS : S.Nonempty) :
  ((num_roots_over_domain P S : ℚ≥0) / (S.card : ℚ≥0))
    ≤ (P.natDegree : ℚ≥0) / (S.card : ℚ≥0) := by
  classical
  -- First, count inequality in ℕ.
  have hcount : num_roots_over_domain P S ≤ P.natDegree :=
    num_roots_over_domain_le_natDegree (S := S) hp
  -- Coerce to `ℚ≥0` and divide both sides by `|S|`.
  have hcount' : (num_roots_over_domain P S : ℚ≥0)
                 ≤ (P.natDegree : ℚ≥0) := by
    exact_mod_cast hcount
  have hden_nonneg : 0 ≤ (S.card : ℚ≥0) := by
    simpa using (bot_le : (⊥ : ℚ≥0) ≤ (S.card : ℚ≥0))
  -- Multiply both sides by `(S.card)⁻¹` (nonnegative), i.e. divide by `|S|`.
  simpa [div_eq_mul_inv] using
    (mul_le_mul_of_nonneg_right hcount' (by simpa using inv_nonneg.mpr hden_nonneg))
