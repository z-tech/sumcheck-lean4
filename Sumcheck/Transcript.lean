import CompPoly.CMvPolynomial

import Sumcheck.Prover
import Sumcheck.Verifier

structure Transcript (𝔽 : Type _) (n : ℕ) [CommRing 𝔽] where
  round_polys : Fin n → (CPoly.CMvPolynomial 1 𝔽)
  challenges : Fin n → 𝔽
  claims : Fin (n + 1) → 𝔽

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

def build_transcript
  {𝔽} {n} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (claim_p  : CPoly.CMvPolynomial n 𝔽)
  (initial_claim : 𝔽)
  (challenges : Fin n → 𝔽) : Transcript 𝔽 n :=
by
  -- compute the round_polys
  let round_polys : Fin n → CPoly.CMvPolynomial 1 𝔽 :=
    fun i => prover_message claim_p (challenge_subset challenges i) (Nat.succ_le_of_lt i.isLt)
  -- use round_polys to compute claims
  let claims: Fin (n + 1) → 𝔽 := derive_claims initial_claim round_polys challenges
  exact {
    round_polys := round_polys
    challenges  := challenges
    claims      := claims
  }

def is_accepts
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽)
  (t : Transcript 𝔽 n) : Bool :=
  -- check all rounds
  (List.finRange n).all (fun i : Fin n =>
    verifier_check (t.claims (Fin.castSucc i)) (t.round_polys i)
    &&
    decide (t.claims i.succ = next_claim (t.challenges i) (t.round_polys i))
  )
  &&
  -- final check
  decide (t.claims (Fin.last n) = CPoly.CMvPolynomial.eval t.challenges p)

namespace __TranscriptTests__
  -- 3x0x1 + 5x0 + 1
  def claim_poly : CPoly.CMvPolynomial 2 (ZMod 19) :=
    CPoly.Lawful.fromUnlawful <|
      ((0 : CPoly.Unlawful 2 (ZMod 19)).insert ⟨#[1, 1], by decide⟩ (3 : ZMod 19))
        |>.insert ⟨#[1, 0], by decide⟩ (5 : ZMod 19)
        |>.insert ⟨#[0, 0], by decide⟩  (1 : ZMod 19)
  def claim : (ZMod 19) := (17 : ZMod 19)
  def simulated_challenges := ![(2 : ZMod 19), (3 : ZMod 19)]

  def valid_transcript := build_transcript claim_poly claim simulated_challenges
  lemma valid_transcript_accepts : is_accepts claim_poly valid_transcript = true := by
    unfold is_accepts
    simp
    native_decide

  def invalid_transcript := build_transcript claim_poly (claim + 1) simulated_challenges
  lemma invalid_transcript_rejects : is_accepts claim_poly invalid_transcript = false := by
    unfold is_accepts
    simp
    native_decide
end __TranscriptTests__
