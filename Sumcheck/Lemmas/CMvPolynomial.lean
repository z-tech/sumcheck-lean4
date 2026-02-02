import CompPoly.CMvPolynomial

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
