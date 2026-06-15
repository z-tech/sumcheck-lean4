/-!
# `DomainEncoded S` — per-call-site scope encoding

Mirrors the Rust trait
[`ark_interop::DomainEncoded`](https://github.com/z-tech/z/blob/main/crates/interoperability/src/hasher.rs#L136).

Concrete hashers carry a `UInt64` domain field as instance state — never
as a trait-method argument, so callers cannot forget DS. Consumer
crates define their own scope vocabulary (`MerkleNode { layer, index,
tree_id }`, `FsLabel`, …) and implement `DomainEncoded` for them; the
concrete hasher's `with_scope` constructor consumes the scope value
through this trait. End users never type a raw `UInt64`.

## Injectivity discipline

The encoding must be **injective on a single consumer's scope space**
for domain separation to work: two distinct call sites must produce
distinct domain values. Cross-consumer collisions are possible
(`MerkleNode { layer := 0, index := 0 }` from `VectorCommitment` and
`FsLabel "x"` from `InteractiveProtocol` could collide); consumers
sharing one hasher instance across protocol layers should reserve
disjoint `UInt64` ranges or use a higher-order tag.
-/

namespace Hasher

/-- Encoding of a per-call-site scope into the `UInt64` domain space
    that concrete hashers consume.

    Implement this for your consumer's scope vocabulary; pass instances
    to the concrete hasher's scope-typed constructor. -/
class DomainEncoded (S : Type) where
  /-- Encode this scope into the `UInt64` domain space. -/
  toDomain : S → UInt64

/-- The identity instance: `UInt64` encodes itself. -/
instance : DomainEncoded UInt64 where
  toDomain n := n

end Hasher
