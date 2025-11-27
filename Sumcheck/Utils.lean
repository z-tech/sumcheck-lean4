import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.CommRing

def eval_at {𝔽} [CommRing 𝔽] (x : 𝔽) (p : MvPolynomial (Fin 1) 𝔽) : 𝔽 :=
  MvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ => x) p
