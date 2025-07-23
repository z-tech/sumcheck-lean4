import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Data.Finset.Lattice.Basic

noncomputable def arity {σ R : Type*} [DecidableEq σ] [CommSemiring R]
  (p : MvPolynomial σ R) : ℕ :=
  p.vars.card

@[simp]
lemma arity_zero {σ R : Type*} [DecidableEq σ] [CommSemiring R] :
  arity (0 : MvPolynomial σ R) = 0 := by
  simp [arity]

lemma arity_add {σ R : Type*} [DecidableEq σ] [CommSemiring R]
  (p q : MvPolynomial σ R) :
  arity (p + q) ≤ arity p + arity q := by
  simp only [arity]
  calc
    (p + q).vars.card
        ≤ (p.vars ∪ q.vars).card := Finset.card_mono (MvPolynomial.vars_add_subset p q)
    _   ≤ p.vars.card + q.vars.card   := Finset.card_union_le _ _

noncomputable def inst {σ R : Type*} [DecidableEq σ] [CommSemiring R]
  (p : MvPolynomial σ R) (θ : σ →₀ R) : MvPolynomial σ R :=
  MvPolynomial.eval₂Hom (MvPolynomial.C : R →+* MvPolynomial σ R) (fun i => MvPolynomial.C (θ i)) p
