import Mathlib.Data.Rat.Init
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Filter

/-!
# Public-Coin Interactive Protocols

This module defines a generic interface for **public-coin interactive protocols** (IPs).
A public-coin IP is one where the verifier's messages are simply random field elements
(challenges). This is the class of protocols to which the Fiat-Shamir transformation
applies.

## Design Choices

- **Round-dependent message types**: `ProverMessage` is indexed by `Fin n`, allowing
  each round to have a different prover message type (e.g., different polynomial arities).
- **Adaptive prover**: The prover at round `i` sees all challenges from rounds `0..i-1`.
- **Completeness and soundness** are both defined generically.

## Architecture

This module is protocol-agnostic. Concrete protocols (e.g., sumcheck) instantiate the
`PublicCoinProtocol` structure. The Fiat-Shamir transformation (in `FiatShamir.lean`) is
proved generically over this interface.
-/

/-- A public-coin interactive protocol with `n` rounds over a challenge type `C`.

In each round `i : Fin n`:
1. The prover sends a message of type `ProverMessage i`
2. The verifier responds with a random challenge of type `C`

After all rounds, the verifier makes a decision based on the full transcript.

Parameters:
- `S`: the type of public instances (statements)
- `C`: the type from which challenges are uniformly sampled
- `n`: the number of rounds -/
structure PublicCoinProtocol (S : Type*) (C : Type*) (n : ℕ) where
  /-- The type of the prover's message at round `i`.
      This is round-dependent: different rounds may use different message types. -/
  ProverMessage : Fin n → Type*
  /-- The full transcript of the interaction: all prover messages and challenges. -/
  Transcript : Type*
  /-- Construct a transcript from its components. -/
  mkTranscript : (∀ i : Fin n, ProverMessage i) → (Fin n → C) → Transcript
  /-- Extract the verifier challenges from a transcript. -/
  challenges : Transcript → (Fin n → C)
  /-- Extract the prover's message at round `i` from a transcript. -/
  proverMessage : Transcript → (i : Fin n) → ProverMessage i
  /-- The verifier's acceptance predicate: given a statement and transcript,
      does the verifier accept? -/
  verifier_accepts : S → Transcript → Prop
  /-- The verifier's decision is decidable (needed for probability counting). -/
  verifier_decides : ∀ (st : S) (tr : Transcript), Decidable (verifier_accepts st tr)
  /-- Round-trip: building a transcript and extracting challenges gives back
      the original challenges. -/
  challenges_mk : ∀ msgs chs, challenges (mkTranscript msgs chs) = chs
  /-- Round-trip: building a transcript and extracting a prover message gives back
      the original message. -/
  proverMessage_mk : ∀ msgs chs i, proverMessage (mkTranscript msgs chs) i = msgs i

/-- An adaptive (potentially dishonest) prover for a public-coin protocol.

At round `i`, the prover sees the statement and all challenges from
previous rounds `0..i-1`, and produces a message of type `ProverMessage i`.

This captures the most general adversarial strategy: the prover can
adaptively choose each message based on all prior verifier challenges. -/
structure Prover {S C : Type*} {n : ℕ} (ip : PublicCoinProtocol S C n) where
  /-- Given a statement, a round index, and the challenges seen so far,
      produce a prover message for this round. -/
  respond : S → (i : Fin n) → (Fin i.val → C) → ip.ProverMessage i

/-- The prefix of challenges visible to the prover at round `i`:
    challenges `0, 1, ..., i-1`. -/
def challengePrefix {C : Type*} {n : ℕ} (r : Fin n → C) (i : Fin n) : Fin i.val → C :=
  fun j => r ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩

/-- Generate the transcript produced by a (potentially dishonest) prover
    interacting with random challenges `r`. -/
def generateTranscript {S C : Type*} {n : ℕ}
    (ip : PublicCoinProtocol S C n)
    (st : S) (P : Prover ip) (r : Fin n → C) : ip.Transcript :=
  ip.mkTranscript (fun i => P.respond st i (challengePrefix r i)) r

/-! ## Probability over challenges -/

/-- The set of all possible challenge vectors of length `n` over `C`. -/
abbrev allChallenges (C : Type*) (n : ℕ) [Fintype C] : Finset (Fin n → C) :=
  Finset.univ

/-- The probability that an event holds over uniformly random challenges. -/
noncomputable def probEvent
    {C : Type*} {n : ℕ} [Fintype C]
    (E : (Fin n → C) → Prop) : ℚ := by
  classical
  let Ω : Finset (Fin n → C) := allChallenges C n
  exact ((Ω.filter E).card : ℚ) / (Ω.card : ℚ)

/-- The probability the verifier accepts when interacting with prover `P`
    on statement `st`, over uniformly random challenges. -/
noncomputable def probAccept {S C : Type*} {n : ℕ} [Fintype C]
    (ip : PublicCoinProtocol S C n)
    (st : S) (P : Prover ip) : ℚ :=
  probEvent (C := C) (n := n)
    (fun r => ip.verifier_accepts st (generateTranscript ip st P r))

/-! ## Soundness and Completeness -/

/-- A public-coin interactive protocol has **soundness error** `ε` with respect to
    a validity predicate `isTrue` if: for every cheating prover `P` and every
    false statement `st`, the probability the verifier accepts is at most `ε`.

    This is the key property that the Fiat-Shamir transformation preserves
    (in the Random Oracle Model). -/
def hasSoundnessError {S C : Type*} {n : ℕ} [Fintype C]
    (ip : PublicCoinProtocol S C n)
    (isTrue : S → Prop) (ε : ℚ) : Prop :=
  ∀ (st : S) (P : Prover ip),
    ¬ isTrue st →
    probAccept ip st P ≤ ε

/-- A public-coin interactive protocol has **perfect completeness** with respect to
    a validity predicate `isTrue` and an honest prover if:
    for every true statement, the verifier always accepts. -/
def hasPerfectCompleteness {S C : Type*} {n : ℕ} [Fintype C]
    (ip : PublicCoinProtocol S C n)
    (isTrue : S → Prop) (honest : Prover ip) : Prop :=
  ∀ (st : S),
    isTrue st →
    probAccept ip st honest = 1

/-- A weaker version: **statistical completeness** with completeness error `δ`.
    For every true statement, the honest prover is accepted with probability ≥ 1 - δ. -/
def hasCompletenessError {S C : Type*} {n : ℕ} [Fintype C]
    (ip : PublicCoinProtocol S C n)
    (isTrue : S → Prop) (honest : Prover ip) (δ : ℚ) : Prop :=
  ∀ (st : S),
    isTrue st →
    probAccept ip st honest ≥ 1 - δ
