-- The abstract `VectorCommitment` typeclass; mirrors ark-vc/src/vc.rs.
-- See VectorCommitment/DESIGN.md §3.3.

class VectorCommitment (V : Type) where
  Alphabet         : Type
  Index            : Type
  UniversalParams  : Type
  CommitterKey     : Type
  VerifierKey      : Type
  Commitment       : Type
  CommitmentState  : Type
  Proof            : Type
  setup  : (maxLen maxQueries : Nat) → ULift.{0} UInt64 → UniversalParams
  trim   : UniversalParams → (len queries : Nat) → CommitterKey × VerifierKey
  commit : CommitterKey → List Alphabet → Commitment × CommitmentState
  «open» : CommitterKey → List Alphabet → Commitment → List Index → List Alphabet →
           CommitmentState → Proof
  check  : VerifierKey → Commitment → List Index → List Alphabet → Proof → Bool

-- Hiding extension. Mirrors ark-vc/src/vc.rs `HidingVectorCommitment` trait.
--
-- The hiding commit takes its randomness *explicitly*, as a typed value drawn
-- from a per-key `Randomness` family (e.g. an exact-length vector of fresh
-- per-leaf salts), so the ideal independent salts are represented directly.
-- The base `VectorCommitment` operations already cover `setup`, `trim`, `open`,
-- and `check`; only the commit step changes under hiding.
class HidingVectorCommitment (V : Type) extends VectorCommitment V where
  /-- The space of hiding randomness for a given committer key (e.g. an
      exact-length vector of fresh per-leaf salts). -/
  Randomness : VectorCommitment.CommitterKey V → Type
  /-- Commit while consuming explicit hiding randomness. -/
  commit_hiding :
    (ck : VectorCommitment.CommitterKey V) → List (VectorCommitment.Alphabet V) →
      Randomness ck →
      VectorCommitment.Commitment V × VectorCommitment.CommitmentState V
