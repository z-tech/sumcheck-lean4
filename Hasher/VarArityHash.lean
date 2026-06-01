/-!
# `VarArityHash H` — variable-arity hashing

Mirrors the Rust trait
[`ark_interop::VarArityHash`](https://github.com/z-tech/z/blob/main/crates/interoperability/src/hasher.rs#L112).

"Reach for it when your shape is genuinely variable" — Fiat–Shamir
transcripts (each absorb has variable byte/field length depending on
the protocol message), variable-arity Merkle compression, and the rare
call site that has no fixed arity.

**Prefer shape-tight traits** ([`Compress K`](Compress.lean),
[`HashValue`](HashValue.lean)) when your shape is fixed. Variable arity
carries the most security footguns — padding rules, length-extension
attacks, encoding choices — reach for it only when nothing else fits.

Domain separation lives in instance state; see
[`Hasher.DomainEncoded`](DomainEncoded.lean).
-/

namespace Hasher

/-- Variable-arity hashing: `List Input → Digest`.

    Used for Fiat–Shamir transcripts (variable-length absorbs) and any
    other genuinely-variable call site. Prefer `Compress K` /
    `HashValue` when arity is fixed. -/
class VarArityHash (H : Type) where
  /-- The input element type. -/
  Input : Type
  /-- The digest type. -/
  Digest : Type
  /-- Digests must be decidable-equal. -/
  decEqDigest : DecidableEq Digest
  /-- Hash an arbitrary-length input list into a digest. -/
  hashVar : H → List Input → Digest

end Hasher
