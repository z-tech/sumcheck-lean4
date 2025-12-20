import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.CommRing

@[simp]
def eval_at {𝔽} [CommRing 𝔽] (x : 𝔽) (p : MvPolynomial (Fin 1) 𝔽) : 𝔽 :=
  MvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ => x) p

@[simp] lemma eval_at_C {𝔽} [CommRing 𝔽] (a x : 𝔽) :
  eval_at x (MvPolynomial.C a) = a :=
  by simp [eval_at, MvPolynomial.eval₂_C]

@[simp] lemma eval_at_X {𝔽} [CommRing 𝔽] (x : 𝔽) :
  eval_at x (MvPolynomial.X 0) = x :=
  by simp [eval_at, MvPolynomial.eval₂_X]

@[simp] lemma eval_at_add {𝔽} [CommRing 𝔽] (p q : MvPolynomial (Fin 1) 𝔽) (x : 𝔽) :
  eval_at x (p + q) = eval_at x p + eval_at x q :=
  by simp [eval_at, MvPolynomial.eval₂_add]

@[simp] lemma eval_at_mul {𝔽} [CommRing 𝔽] (p q : MvPolynomial (Fin 1) 𝔽) (x : 𝔽) :
  eval_at x (p * q) = eval_at x p * eval_at x q :=
  by simp [eval_at, MvPolynomial.eval₂_mul]

@[simp] lemma eval_at_sub {𝔽} [CommRing 𝔽] (p q : MvPolynomial (Fin 1) 𝔽) (x : 𝔽) :
  eval_at x (p - q) = eval_at x p - eval_at x q :=
  by simp [eval_at, MvPolynomial.eval₂_sub]
