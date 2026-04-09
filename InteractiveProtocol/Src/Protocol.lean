import Mathlib.Data.Rat.Init

-- Here we define an interface for public-coin interactive protocols
-- verifier messages are simply challenges (random field elements)
-- the Fiat-Shamir transformation applies to this class of protocols

-- round messages (from the prover) can be different types
-- prover is "adaptive" meaning it sees all challenges from rounds 0..i-1

-- the idea is that concrete protocols like sumcheck can instantiate this structure
-- and that FiatShamir is formalized generically over this interface

-- S is the statement (public instance)
-- C is the type from which challenges are uniformly sampled
-- n is the number of rounds

structure PublicCoinProtocol (S : Type*) (C : Type*) (n : ℕ) where
  ProverMessage : Fin n → Type*
  Transcript : Type*
  mkTranscript : (∀ i : Fin n, ProverMessage i) → (Fin n → C) → Transcript
  challenges : Transcript → (Fin n → C)
  proverMessage : Transcript → (i : Fin n) → ProverMessage i
  verifier_accepts : S → Transcript → Prop
  verifier_decides : ∀ (st : S) (tr : Transcript), Decidable (verifier_accepts st tr)
  challenges_mk : ∀ msgs chs, challenges (mkTranscript msgs chs) = chs
  proverMessage_mk : ∀ msgs chs i, proverMessage (mkTranscript msgs chs) i = msgs i

-- an adaptive (potentially dishonest) prover
-- at round i, sees the statement and all challenges from rounds 0..i-1
structure Prover {S C : Type*} {n : ℕ} (ip : PublicCoinProtocol S C n) where
  respond : S → (i : Fin n) → (Fin i.val → C) → ip.ProverMessage i

-- generate the transcript from a prover interacting with random challenges
-- at round i, the prover sees challenges 0, 1, ..., i-1
def generateTranscript {S C : Type*} {n : ℕ}
    (ip : PublicCoinProtocol S C n)
    (st : S) (P : Prover ip) (r : Fin n → C) : ip.Transcript :=
  ip.mkTranscript (fun i => P.respond st i (fun j => r ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩)) r
