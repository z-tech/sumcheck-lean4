import CompPoly.CMvPolynomial

import Sumcheck.Src.Transcript
import Sumcheck.Src.HonestTranscript
import Sumcheck.Models.Adversary

def AdversaryTranscript
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (claim : 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (adversary : Adversary 𝔽 n)
  (r : Fin n → 𝔽) : Transcript 𝔽 n :=
by
  let round_polys : Fin n → CPoly.CMvPolynomial 1 𝔽 :=
    fun i => adversary p claim i (challenge_subset r i)
  let claims : Fin (n + 1) → 𝔽 := generate_honest_claims claim round_polys r
  exact { round_polys := round_polys, challenges := r, claims := claims }
