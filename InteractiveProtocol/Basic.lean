import Mathlib.Data.Rat.Init
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Filter

-- Here we define an interface for public-coin interactive protocols
-- verifier messages are simply challenges (random field elements)
-- the Fiat-Shamir transformation applies to this class of protocols

-- round messages (from the prover) can be different types
-- prover is "adaptive" meaning it sees all challenges from rounds 0..i-1
-- we define completeness and soundness generically

-- the idea is that concrete protocols like sumcheck can instantiate this structure
-- and that FiatShamir is formalized generically over this interface

-- S is the statement (public instance)
-- C is the type from which challenges are uniformly sampled
-- n is the number of rounds

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

/-- Generate the transcript produced by a (potentially dishonest) prover
    interacting with random challenges `r`.
    At round `i`, the prover sees challenges `0, 1, ..., i-1`. -/
def generateTranscript {S C : Type*} {n : ℕ}
    (ip : PublicCoinProtocol S C n)
    (st : S) (P : Prover ip) (r : Fin n → C) : ip.Transcript :=
  ip.mkTranscript (fun i => P.respond st i (fun j => r ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩)) r

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
    (isTrue : S → Prop) (ε : S → ℚ) : Prop :=
  ∀ (st : S) (P : Prover ip),
    ¬ isTrue st →
    probAccept ip st P ≤ ε st

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
