/-
Copyright (c) 2026 LeanStuff contributors. All rights reserved.
-/
import VectorCommitment.Properties.Probability.ROHasher
import VectorCommitment.Src.Merkle.Scheme

/-!
# `Verify^H` as an oracle computation, and the straightline cache extractor

The **shared-oracle** form of Merkle verification: instead of calling a stored
hasher, it recomputes the root by *querying* the lazily-sampled random oracle,
mirroring `MerkleCommitment.reconstructRoot` / `MerkleCommitment.check` with
`query (encode…)` in place of `hashLeaf` / `hashNodes`. The ROM security
experiments validate an adversary's break against the *same* `H` it queried, so
the winning event cannot be decoupled from the oracle.

`cacheExtract` is the dual straightline extractor: it reads the finished
`QueryLog` and walks the digest tree top-down to recover the committed leaf.
-/

namespace ROHasher

open OracleComp

/-- Walk the bottom-up copath, querying the oracle for each internal node.
    Mirrors `MerkleCommitment.walkCopath` / `combineUp`: at `pos` the
    accumulator is the left child iff `pos` is odd. -/
noncomputable def walkCopathOracle {κ : Nat} :
    Nat → List.Vector Bool κ → List (List.Vector Bool κ) →
      OracleComp (MerkleROSpec κ) (List.Vector Bool κ)
  | _,   acc, []          => pure acc
  | pos, acc, sib :: rest => do
      let children := if pos % 2 = 1 then [acc, sib] else [sib, acc]
      let parent ← query (encodeNodes children)
      walkCopathOracle ((pos - 1) / 2) parent rest

/-- Reconstruct a root from one `(i, value, salt, copath)` by querying the
    shared oracle. Mirrors `MerkleCommitment.reconstructRoot` (leaf vertex
    `n - 1 + i` for an `n`-leaf tree). -/
noncomputable def reconstructRootOracle {κ : Nat} (n i : Nat)
    (value salt : List.Vector Bool κ) (copath : List (List.Vector Bool κ)) :
    OracleComp (MerkleROSpec κ) (List.Vector Bool κ) := do
  let leaf ← query (encodeLeaf value salt)
  walkCopathOracle (n - 1 + i) leaf copath

/-- `Verify^H` for a Merkle opening of an `n`-leaf tree: every
    `(index, value, entry)` triple must reconstruct, via shared-oracle queries,
    to `root`. Mirrors `MerkleCommitment.check`. -/
noncomputable def checkOracle {κ : Nat} (n : Nat) (root : List.Vector Bool κ)
    (op : Opening (ROHasherValue κ)) (pf : OpeningProof (ROHasherValue κ)) :
    OracleComp (MerkleROSpec κ) Bool :=
  if op.indices.length ≠ op.values.length ∨ op.indices.length ≠ pf.entries.length then
    pure false
  else
    ((op.indices.zip op.values).zip pf.entries).foldlM
      (fun acc triple => do
        let ((i, value), (salt, copath)) := triple
        let r ← reconstructRootOracle n i value salt copath
        pure (acc && decide (r = root) && decide (copath.length = PerfectBinary.log2Floor n)))
      true

-- ---------------------------------------------------------------------------
-- Straightline cache extractor: read the finished QueryLog top-down.
-- ---------------------------------------------------------------------------

/-- Decode one serialized child digest (`κ` bytes, each `0`/`1`) back to a
    bit-vector — inverse of the per-child serialization in `encodeNodes`. -/
def decodeDigest {κ : Nat} (b : ByteArray) : Option (List.Vector Bool κ) :=
  let bits : List Bool := b.toList.map (fun byte => decide (byte = 1))
  if h : bits.length = κ then some ⟨bits, h⟩ else none

/-- Parse a query input as an internal-node query: NODE tag, then each
    remaining byte array decodes to a child digest. -/
def decodeNodeInput {κ : Nat} (input : List ByteArray) :
    Option (List (List.Vector Bool κ)) :=
  match input with
  | tag :: rest => if tag == Tag.node then rest.mapM decodeDigest else none
  | []          => none

/-- Root→leaf child choices (`0` = left, `1` = right) for message index `i` in
    an `n`-leaf tree over `depth` levels. -/
def descentChoices (n i depth : Nat) : List Nat :=
  let rec go (v : Nat) (fuel : Nat) (acc : List Nat) : List Nat :=
    match fuel with
    | 0          => acc
    | Nat.succ f =>
        if v = 0 then acc
        else go ((v - 1) / 2) f ((if v % 2 = 1 then 0 else 1) :: acc)
  go (n - 1 + i) depth []

/-- Descend the cached digest tree following `choices`, returning the leaf
    query's (tagged) input. `none` if a required digest is absent or a node
    fails to decode. -/
def cacheExtractAux {κ : Nat} (log : QueryLog (MerkleROSpec κ))
    (digest : List.Vector Bool κ) (choices : List Nat) : Option (List ByteArray) :=
  let entries : List ((MerkleROSpec κ).Domain × (MerkleROSpec κ).Range) := log
  match entries.find? (fun e => decide (e.2 = digest)) with
  | none   => none
  | some e =>
    match choices with
    | []        => some e.1
    | c :: rest =>
      match decodeNodeInput e.1 with
      | some children =>
        match children[c]? with
        | some child => cacheExtractAux log child rest
        | none       => none
      | none => none
termination_by choices.length
decreasing_by simp_wf

/-- **Straightline cache extractor** for an `n`-leaf Merkle tree: walk the query
    log from `root` toward leaf message-index `i`, returning the committed leaf
    input (or `none`). The descent length is the tree depth `⌊log₂ n⌋`. -/
def cacheExtract {κ : Nat} (log : QueryLog (MerkleROSpec κ))
    (root : List.Vector Bool κ) (n i : Nat) : Option (List ByteArray) :=
  cacheExtractAux log root (descentChoices n i (PerfectBinary.log2Floor n))

end ROHasher
