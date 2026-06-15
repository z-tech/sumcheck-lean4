import VectorCommitment.Src.Merkle.Scheme

/-!
# Monomorphized refinement-target naming for Merkle

The hax-extracted Rust `ark-merkle-commitment` crate needs **stable
named Lean symbols** to refine into. This file defines exactly that:
`commit_concrete`, `open_concrete`, `check_concrete` are
shape-specialised (to `PerfectBinary`) wrappers around the abstract
`MerkleCommitment.commit/open/check` from
[`Scheme.lean`](Scheme.lean), with `:= rfl` refinement theorems.

## Architecture (1a — additive)

The refinement target architecture this file embodies:

1. **Primary refinement anchor** — `commit_concrete` /
   `open_concrete` / `check_concrete` here. The Rust crate's
   hax-extracted `commit` / `open` / `check` refine into these names.
   Trivially equal to `MerkleCommitment.*` by `rfl`, so any theorem
   proven about the abstract `MerkleCommitment` (binding, completeness,
   extractability, etc.) transfers directly.

2. **Secondary refinement anchor** — the abstract trait dispatch
   `VectorCommitment.commit/open/check` from
   [`Instance.lean`](Instance.lean). Available for downstream
   non-Merkle backends (KZG, Pedersen, lattice) that want to bind on
   `[VectorCommitment V]` abstractly. Verified runnable end-to-end by
   [`Tests/TraitTests.lean`](../../Tests/TraitTests.lean).

Both are valid. The primary anchor is preferred for the immediate Rust
extraction because it avoids any typeclass projection chain — hax sees
a fully-named symbol with the shape baked in.

## Concrete hasher (decision 2c)

This file does **not** monomorphize over a specific hasher (Blake3,
Poseidon2, …). Concrete hashers live in the consumer crate's own
`proofs/lean/` tree per the spec-upstream / instance-downstream pattern
[`ark-transforms`](https://github.com/z-tech/z) and `ark-polynomials`
already use. The Rust crate's `proofs/lean/` instantiates
`[MerkleHasher Blake3Hasher]` (or Poseidon2, …) and applies
`commit_concrete` with `H := Blake3Hasher`. The hax-extracted Rust
refines into `VectorCommitment.Refinement.commit_concrete` with the
concrete `H` substituted at the call site.
-/

namespace VectorCommitment.Refinement

variable {H : Type} [MerkleHasher H]

-- ---------------------------------------------------------------------------
-- Refinement anchors: shape-specialised wrappers + `rfl` equivalences
-- ---------------------------------------------------------------------------

/-- Refinement-anchor name for `MerkleCommitment.commit` specialised
    to the `PerfectBinary` shape. The Rust crate's hax-extracted
    `commit` refines into this symbol. -/
def commit_concrete (mc : MerkleCommitment H PerfectBinary)
    (msg : List (MerkleHasher.Symbol H)) :
    Committed H PerfectBinary × Trapdoor H PerfectBinary :=
  mc.commit msg

/-- Definitional equivalence: `commit_concrete` is exactly
    `MerkleCommitment.commit` at the `PerfectBinary` shape. Any
    theorem proven about the abstract `commit` transfers through
    this rewrite. -/
theorem commit_concrete_eq (mc : MerkleCommitment H PerfectBinary)
    (msg : List (MerkleHasher.Symbol H)) :
    commit_concrete mc msg = mc.commit msg := rfl

/-- Refinement-anchor name for `MerkleCommitment.open` specialised
    to the `PerfectBinary` shape. -/
def open_concrete (mc : MerkleCommitment H PerfectBinary)
    (msg : List (MerkleHasher.Symbol H))
    (td : Trapdoor H PerfectBinary) (indices : List Nat) :
    OpeningProof H :=
  mc.open msg td indices

theorem open_concrete_eq (mc : MerkleCommitment H PerfectBinary)
    (msg : List (MerkleHasher.Symbol H))
    (td : Trapdoor H PerfectBinary) (indices : List Nat) :
    open_concrete mc msg td indices = mc.open msg td indices := rfl

/-- Refinement-anchor name for `MerkleCommitment.check` specialised
    to the `PerfectBinary` shape. -/
def check_concrete (mc : MerkleCommitment H PerfectBinary)
    (root : MerkleHasher.Digest H)
    (op : Opening H) (pf : OpeningProof H) : Bool :=
  mc.check root op pf

theorem check_concrete_eq (mc : MerkleCommitment H PerfectBinary)
    (root : MerkleHasher.Digest H)
    (op : Opening H) (pf : OpeningProof H) :
    check_concrete mc root op pf = mc.check root op pf := rfl

end VectorCommitment.Refinement
