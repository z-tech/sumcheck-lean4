import Mathlib.Data.Vector.Basic

/-!
# `Compress (K : Nat) (H : Type)` — K-to-1 compression

Mirrors the Rust trait
[`ark_interop::Compress<const K: usize>`](https://github.com/z-tech/z/blob/main/crates/interoperability/src/hasher.rs#L82).

A `Compress K H` instance for a hasher type `H` provides a shape-tight
K-to-1 compression `[Digest; K] → Digest`. This is the trait Merkle
internal-node hashing binds on (`K = 2` for binary trees, `K = k` for
k-ary trees), and any other call site whose compression arity is fixed
and known at construction time.

Domain separation is **not** a method argument: each concrete hasher
instance carries its domain as instance state (see
[`Hasher.DomainEncoded`](DomainEncoded.lean)). Trait method `compress`
takes only `(self, children)` so callers cannot forget DS.

## When to use what

| Trait | Shape | Use for |
|---|---|---|
| `Compress K`            | `Vector Digest K → Digest` | Merkle internal nodes, fixed-arity compression |
| [`HashValue`](HashValue.lean) | `Input → Digest`           | Merkle leaves, single-purpose 1-to-1 hashes  |
| [`VarArityHash`](VarArityHash.lean) | `List Input → Digest`  | Fiat–Shamir transcripts, genuinely variable arity |

Prefer the shape-tight `Compress K` / `HashValue` traits when the arity
is fixed. Variable arity carries the most security footguns (padding
rules, length-extension, encoding choices) — reach for it only when
nothing else fits.
-/

namespace Hasher

/-- K-to-1 hash compression: `[Digest; K] → Digest`.

    `K` is a compile-time arity. `H` is the hasher value type; an
    instance fixes the digest type and provides the compression
    function. -/
class Compress (K : Nat) (H : Type) where
  /-- The digest type. -/
  Digest : Type
  /-- Digests must be decidable-equal (so checks like `commitment.root = h`
      work computationally). -/
  decEqDigest : DecidableEq Digest
  /-- Compress `K` children into one digest. -/
  compress : H → List.Vector Digest K → Digest

end Hasher
