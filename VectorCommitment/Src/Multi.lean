import VectorCommitment.Src.Trait
import Mathlib.Data.Vector.Basic

-- Multi-vector commitment trait. Mirrors ark-vc/src/mvc.rs.

class MultiVectorCommitment (V : Type) extends VectorCommitment V where
  setup_multiple  : (maxLen maxQueries maxVectors : Nat) → ULift.{0} UInt64 →
                    VectorCommitment.UniversalParams V
  trim_multiple   : VectorCommitment.UniversalParams V →
                    (len queries vectors : Nat) →
                    VectorCommitment.CommitterKey V × VectorCommitment.VerifierKey V
  commit_multiple : VectorCommitment.CommitterKey V →
                    List (List (VectorCommitment.Alphabet V)) →
                    List (VectorCommitment.Commitment V) ×
                      List (VectorCommitment.CommitmentState V)
  open_multiple   : VectorCommitment.CommitterKey V →
                    List (List (VectorCommitment.Alphabet V)) →
                    List (VectorCommitment.Commitment V) →
                    List (List (VectorCommitment.Index V)) →
                    List (List (VectorCommitment.Alphabet V)) →
                    List (VectorCommitment.CommitmentState V) →
                    VectorCommitment.Proof V
  check_multiple  : VectorCommitment.VerifierKey V →
                    List (VectorCommitment.Commitment V) →
                    List (List (VectorCommitment.Index V)) →
                    List (List (VectorCommitment.Alphabet V)) →
                    VectorCommitment.Proof V → Bool

-- The hiding multi-commit takes an *exact-length* vector of per-commit hiding
-- randomness, one independent draw per committed vector. The base
-- `MultiVectorCommitment` already covers open/check.
class HidingMultiVectorCommitment (V : Type) extends
    MultiVectorCommitment V, HidingVectorCommitment V where
  commit_multiple_hiding :
    (ck : VectorCommitment.CommitterKey V) →
    (msgs : List (List (VectorCommitment.Alphabet V))) →
    List.Vector (HidingVectorCommitment.Randomness ck) msgs.length →
    List (VectorCommitment.Commitment V) × List (VectorCommitment.CommitmentState V)
