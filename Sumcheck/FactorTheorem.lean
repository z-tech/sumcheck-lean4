import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Mathlib.FieldTheory.Finite.Basic

open Polynomial

variable {R : Type*} [Field R]

lemma remainder_theorem (p q : Polynomial R) (a r : R) :
  p = (X - C a) * q + C r -> p.eval a = r := by
  intro h
  simp [h, Polynomial.eval_add, Polynomial.eval_mul]

-- lemma division_by_linear_factor_reduces_degree_by_one
--   (p : Polynomial R) (a : R) (_h0 : p ≠ 0) (_h : p.eval a = 0) :
--   ∀ a : R, p.eval a = 0 -> p.natDegree - 1 = (p / (X - C a)).natDegree := by


lemma division_by_linear_factor_reduces_degree_by_one
  (p : Polynomial R) (a : R) (hp : p ≠ 0) (ha : p.eval a = 0) :
  p.natDegree - 1 = (p / (X - C a)).natDegree := by
  classical
  -- remainder is 0 when a is a root
  have hmod : p % (X - C a) = 0 := by
    simpa [ha] using mod_X_sub_C_eq_C_eval (p := p) (a := a)
  -- Euclidean division: p = (p / (X - C a)) * (X - C a)
  have hfac : p = (p / (X - C a)) * (X - C a) := by
    simpa [hmod, add_comm] using div_add_mod p (X - C a)
  have hX : (X - C a) ≠ 0 := X_sub_C_ne_zero a
  have hq : p / (X - C a) ≠ 0 := by
    intro h0; exact hp (by simpa [hfac, h0, zero_mul])
  -- degrees add for nonzero factors
  have hdeg := natDegree_mul hq hX
  rw [hfac, natDegree_X_sub_C, add_comm] at hdeg
  -- rewrite as succ and subtract 1
  rw [←Nat.succ_eq_add_one, Nat.succ_pred_eq_of_pos (natDegree_pos_of_eval_eq_zero hp ha)] at hdeg
  exact (Nat.succ_inj'.mp hdeg).symm
