import CompPoly.CMvPolynomial

import Sumcheck.Impl.Polynomials

def extract_exp_var_i {n : ℕ} (m : CPoly.CMvMonomial n) (i : Fin n) : ℕ :=
  (CPoly.CMvMonomial.toFinsupp m) i

def pow_univariate {𝔽} [CommRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (p : CPoly.CMvPolynomial 1 𝔽) : ℕ → CPoly.CMvPolynomial 1 𝔽
| 0     => c1 1
| (e+1) => p * pow_univariate p e

def subst_monomial {n : ℕ} {𝔽} [CommRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (vs : Fin n → CPoly.CMvPolynomial 1 𝔽) (m : CPoly.CMvMonomial n) :
  CPoly.CMvPolynomial 1 𝔽 :=
(List.finRange n).foldl (fun acc i => acc * pow_univariate (vs i) (extract_exp_var_i m i)) (c1 1)

namespace CPoly

def eval₂Poly
  {n : ℕ} {𝔽} [CommRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (f : 𝔽 → CPoly.CMvPolynomial 1 𝔽)
  (vs : Fin n → CPoly.CMvPolynomial 1 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽) : CPoly.CMvPolynomial 1 𝔽 :=
Std.ExtTreeMap.foldl (fun acc m c => (f c * subst_monomial vs m) + acc) (c1 0) p.1
