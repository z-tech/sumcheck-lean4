import CompPoly.Multivariate.CMvPolynomial
import Sumcheck.Src.Prover

-- the subset of challenges the prover is allowed to see at round i
def challenge_subset {𝔽} {n} (ch : Fin n → 𝔽) (i : Fin n) : Fin i.val → 𝔽 :=
  fun j => ch ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩

-- a sumcheck transcript: the round polynomials and verifier challenges
structure Transcript (𝔽 : Type _) (n : ℕ) [CommRing 𝔽] where
  round_polys : Fin n → (CPoly.CMvPolynomial 1 𝔽)
  challenges : Fin n → 𝔽

-- evaluate a round polynomial at the challenge to get the next round's claim
@[simp] def next_claim {𝔽} [CommRing 𝔽] [DecidableEq 𝔽]
  (round_challenge : 𝔽)
  (round_p : CPoly.CMvPolynomial 1 𝔽) : 𝔽 :=
  CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ => round_challenge) round_p

-- compute the intermediate claims from an initial claim, round polynomials, and challenges
-- claims(0) = initial_claim, claims(k+1) = next_claim(challenges(k), round_polys(k))
def generate_honest_claims
  {𝔽} {n} [CommRing 𝔽] [DecidableEq 𝔽]
  (initial_claim : 𝔽)
  (round_polys : Fin n → CPoly.CMvPolynomial 1 𝔽)
  (challenges : Fin n → 𝔽) : Fin (n+1) → 𝔽
  | ⟨0, _⟩ => initial_claim
  | ⟨k+1, hk⟩ =>
      let i : Fin n := ⟨k, Nat.lt_of_succ_lt_succ hk⟩
      next_claim (challenges i) (round_polys i)

-- compute claims from a transcript and initial claim
def Transcript.claims {𝔽} {n} [CommRing 𝔽] [DecidableEq 𝔽]
  (t : Transcript 𝔽 n) (initial_claim : 𝔽) : Fin (n+1) → 𝔽 :=
  generate_honest_claims initial_claim t.round_polys t.challenges

def generate_honest_transcript
  {𝔽} {n} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (domain : List 𝔽)
  (claim_p  : CPoly.CMvPolynomial n 𝔽)
  (_initial_claim : 𝔽)
  (challenges : Fin n → 𝔽) : Transcript 𝔽 n :=
  { round_polys := fun i => honest_prover_message domain claim_p (challenge_subset challenges i) (Nat.succ_le_of_lt i.isLt)
    challenges := challenges }
