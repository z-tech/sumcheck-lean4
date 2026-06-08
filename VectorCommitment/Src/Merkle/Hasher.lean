-- Mirrors ark-mt/src/hasher.rs:33-58. See VectorCommitment/DESIGN.md §3.1.

class MerkleHasher (H : Type) where
  Symbol : Type
  Digest : Type
  Salt   : Type
  decEqDigest : DecidableEq Digest
  defaultSalt : Inhabited Salt
  -- No `sampleSalt`: hiding randomness is supplied explicitly through
  -- `HidingVectorCommitment.Randomness`, never derived from a finite seed.
  /-- ρ(symbol, salt) at a leaf. -/
  hashLeaf   : H → Symbol → Salt → Digest
  /-- ρ(child₁, …, childₖ) at an internal vertex. -/
  hashNodes  : H → List Digest → Digest
