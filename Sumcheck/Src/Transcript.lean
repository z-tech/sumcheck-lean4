import CompPoly.Multivariate.CMvPolynomial
import Sumcheck.Src.Prover

-- the subset of challenges the prover is allowed to see at round i
def challenge_subset {𝔽} {n} (ch : Fin n → 𝔽) (i : Fin n) : Fin i.val → 𝔽 :=
  fun j => ch ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩

-- The transcript of a sumcheck protocol interaction
structure Transcript (𝔽 : Type _) (n : ℕ) [CommRing 𝔽] where
  round_polys : Fin n → (CPoly.CMvPolynomial 1 𝔽)
  challenges : Fin n → 𝔽
  claims : Fin (n + 1) → 𝔽


-- Attention: when round_p is dishonest, this is not necessarily the genuine next claim
@[simp] def next_claim {𝔽} [CommRing 𝔽] [DecidableEq 𝔽]
  (round_challenge : 𝔽)
  (round_p : CPoly.CMvPolynomial 1 𝔽) : 𝔽 :=
  CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ => round_challenge) round_p

def generate_honest_claims
  {𝔽} {n} [CommRing 𝔽] [DecidableEq 𝔽]
  (initial_claim : 𝔽)
  (round_polys : Fin n → CPoly.CMvPolynomial 1 𝔽)
  (challenges : Fin n → 𝔽) : Fin (n+1) → 𝔽
  | ⟨0, _⟩ => initial_claim
  | ⟨k+1, hk⟩ =>
      let i : Fin n := ⟨k, Nat.lt_of_succ_lt_succ hk⟩
      next_claim (challenges i) (round_polys i)

def generate_honest_transcript
  {𝔽} {n} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (domain : List 𝔽)
  (claim_p  : CPoly.CMvPolynomial n 𝔽)
  (initial_claim : 𝔽)
  (challenges : Fin n → 𝔽) : Transcript 𝔽 n :=
by
  let round_polys : Fin n → CPoly.CMvPolynomial 1 𝔽 :=
    fun i => honest_prover_message domain claim_p (challenge_subset challenges i) (Nat.succ_le_of_lt i.isLt)
  let claims: Fin (n + 1) → 𝔽 := generate_honest_claims initial_claim round_polys challenges
  exact {
    round_polys := round_polys
    challenges  := challenges
    claims      := claims
  }
