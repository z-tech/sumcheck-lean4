import Sumcheck.Impl.HonestProver
import Sumcheck.Impl.Transcript
import Sumcheck.Impl.Verifier

def challenge_subset {𝔽} {n} (ch : Fin n → 𝔽) (i : Fin n) : Fin i.val → 𝔽 :=
  fun j => ch ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩

def derive_claims
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
  (claim_p  : CPoly.CMvPolynomial n 𝔽)
  (initial_claim : 𝔽)
  (challenges : Fin n → 𝔽) : Transcript 𝔽 n :=
by
  let round_polys : Fin n → CPoly.CMvPolynomial 1 𝔽 :=
    fun i => honest_prover_message claim_p (challenge_subset challenges i) (Nat.succ_le_of_lt i.isLt)
  let claims: Fin (n + 1) → 𝔽 := derive_claims initial_claim round_polys challenges
  exact {
    round_polys := round_polys
    challenges  := challenges
    claims      := claims
  }

def is_verifier_accepts_transcript
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽)
  (t : Transcript 𝔽 n) : Bool :=
by
  let rounds_ok : Bool :=
    (List.finRange n).all (fun i : Fin n =>
      verifier_check (ind_degree_k p i) (t.claims (Fin.castSucc i)) (t.round_polys i)
      &&
      decide (t.claims i.succ = next_claim (t.challenges i) (t.round_polys i))
    )
  let final_ok : Bool :=
    decide (t.claims (Fin.last n) = CPoly.CMvPolynomial.eval t.challenges p)
  exact rounds_ok && final_ok
