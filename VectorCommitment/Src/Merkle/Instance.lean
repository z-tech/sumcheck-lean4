import VectorCommitment.Src.Trait
import VectorCommitment.Src.Merkle.Scheme

-- Bridge: the abstract `VectorCommitment` trait realized for `MerkleCommitment H S`.
-- Mirrors ark-mt/src/vc.rs.
--
-- ## Refinement target architecture (additive)
--
-- The Rust `ark-merkle-commitment` crate has two valid refinement targets
-- into Lean:
--   * Preferred / primary: `VectorCommitment.Refinement.{commit,open,check}_concrete`
--     in `Refinement.lean` — shape-specialised, no typeclass projection chain
--     at extraction time, definitionally equal to `MerkleCommitment.*` by `rfl`.
--   * Secondary: the `VectorCommitment.{commit,open,check}` trait-dispatch
--     projections via the instance below — useful for downstream protocols
--     that bind abstractly on `[VectorCommitment V]` (Kilian's Theorem 5.1,
--     BCS soundness, the IOPP compilation, …). Future non-Merkle backends
--     (KZG, Pedersen, lattice) plug in via additional `instance :
--     VectorCommitment KZGCommitment` etc. without touching this file.
--
-- Both anchors are kept available; the Rust crate's hax extraction targets
-- the primary anchor, and abstract protocol theorems consume the secondary.
--
-- Mapping notes:
--   * Merkle has no trusted-setup ceremony, so `UniversalParams`,
--     `CommitterKey`, and `VerifierKey` all carry the `MerkleCommitment H S`
--     itself. `setup` returns `default` from `Inhabited`; downstream callers
--     supply `Inhabited (MerkleCommitment H S)` (trivially provided whenever
--     `H` and `S` are `Inhabited`). This keeps the instance **computable**
--     so the whole `VectorCommitment` dispatch is hax-extractable.
--   * `trim` is a no-op clone; the `len`/`queries` knobs don't shape Merkle.
--   * `commit`/`open`/`check` delegate straight to `MerkleCommitment.*`.
--   * `open` discards the typeclass-supplied `values` argument: the prover
--     already has the whole message in the `Trapdoor`.
--   * `check` rebuilds the `Opening` record from `(indices, values)`.

instance {H S : Type} [MerkleHasher H] [MerkleShape S]
    [Inhabited (MerkleCommitment H S)] :
    VectorCommitment (MerkleCommitment H S) where
  Alphabet         := MerkleHasher.Symbol H
  Index            := Nat
  UniversalParams  := MerkleCommitment H S
  CommitterKey     := MerkleCommitment H S
  VerifierKey      := MerkleCommitment H S
  Commitment       := Committed H S
  CommitmentState  := Trapdoor H S
  Proof            := OpeningProof H
  setup _ _ _      := default
  trim mc _ _      := (mc, mc)
  commit ck msg    := ck.commit msg
  «open» ck _ _ indices _ td := ck.open [] td indices
  check vk commitment indices values proof :=
    vk.check commitment.root { indices := indices, values := values } proof
