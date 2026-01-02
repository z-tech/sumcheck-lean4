import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Data.ZMod.Basic

import Mathlib.Data.Fintype.Card
import Mathlib

import CompPoly
import CompPoly.CMvPolynomial
import CompPoly.CMvMonomial
import CompPoly.Lawful

import Sumcheck.Prover
import Sumcheck.Verifier
import Sumcheck.Polynomials

-- if g != h, the number of inputs x that make g(x) = h(x) is at most deg(g - h) / |𝔽|
-- eq. probability that random challenge makes diff poly q evaluate to zero pr[(g - h)(0) = 0] = deg(g - h) / |𝔽|
lemma one_round_soundness
  {𝔽 : Type _} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (g h : CPoly.CMvPolynomial 1 𝔽)
  (hgh : g ≠ h) :
  (↑{f ∈ Fintype.piFinset (fun _ : Fin 1 => (Finset.univ : Finset 𝔽))
        | CPoly.CMvPolynomial.eval f g = CPoly.CMvPolynomial.eval f h}.card : ℚ)
    / (Fintype.card 𝔽 : ℚ)
  ≤ ((MvPolynomial.totalDegree (CPoly.fromCMvPolynomial g - CPoly.fromCMvPolynomial h) : ℕ) : ℚ)
      / (Fintype.card 𝔽 : ℚ) := by
  classical

  -- `piFinset (fun _ => univ)` is just `univ` on functions
  have hpi :
      (Fintype.piFinset (fun _ : Fin 1 => (Finset.univ : Finset 𝔽)))
        = (Finset.univ : Finset (Fin 1 → 𝔽)) := by
    ext f
    simp

  -- Nonzero on the MvPolynomial side
  have hp :
      (CPoly.fromCMvPolynomial g - CPoly.fromCMvPolynomial h)
        ≠ (0 : MvPolynomial (Fin 1) 𝔽) := by
    intro hp0
    have hfrom : CPoly.fromCMvPolynomial g = CPoly.fromCMvPolynomial h := by
      have : CPoly.fromCMvPolynomial g - CPoly.fromCMvPolynomial h = 0 := by
        simpa using hp0
      exact sub_eq_zero.mp this
    have : g = h :=
      (CPoly.eq_iff_fromCMvPolynomial (u := g) (v := h)).2 hfrom
    exact hgh this

  -- Schwartz–Zippel on the difference polynomial
  have sz :=
    MvPolynomial.schwartz_zippel_totalDegree
      (R := 𝔽)
      (p := CPoly.fromCMvPolynomial g - CPoly.fromCMvPolynomial h)
      hp
      (S := (Finset.univ : Finset 𝔽))

  -- Turn `eval(from g) - eval(from h) = 0` into `eval g = eval h`,
  -- and rewrite `univ` as your `piFinset`.
  simpa [hpi,
        CPoly.eval_equiv (p := g),
        CPoly.eval_equiv (p := h),
        sub_eq_zero,
        pow_one] using sz
