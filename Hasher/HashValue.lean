/-!
# `HashValue H` — 1-to-1 hashing

Mirrors the Rust trait
[`ark_interop::HashValue`](https://github.com/z-tech/z/blob/main/crates/interoperability/src/hasher.rs#L95).

The canonical **Merkle-leaf** trait: a single input value mapped to a
single digest. Also the right trait for any other single-purpose
1-to-1 hash call site (commit-to-a-scalar, hash-a-public-key, …).

`Input` is the value type being hashed — typically a field element `F`
for algebraic hashes (Poseidon), `ByteArray` for bytewise hashes
(Blake3, SHA-256), or `Vector F n` for fixed-length field-element
vector leaves.

Domain separation lives in instance state, not a method argument; see
[`Hasher.DomainEncoded`](DomainEncoded.lean).
-/

namespace Hasher

/-- 1-to-1 hashing: `Input → Digest`.

    Bound by Merkle leaf hashing, single-purpose hash call sites, and
    any 1-to-1 specialisation of compression. -/
class HashValue (H : Type) where
  /-- The input type. -/
  Input : Type
  /-- The digest type. -/
  Digest : Type
  /-- Digests must be decidable-equal. -/
  decEqDigest : DecidableEq Digest
  /-- Hash a single input value into a digest. -/
  hashValue : H → Input → Digest

end Hasher
