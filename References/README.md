# `References/` — reserved

Root-level home for **Lean specs of upstream Rust crypto primitives**.
Reserved per the Rust crates' planned-Lean-port comments — see e.g.
[`z/crates/hasher/src/blake3/mod.rs`](https://github.com/z-tech/z/blob/main/crates/hasher/src/blake3/mod.rs):

> *"When this module is ported to Lean, the spec target will be the
> reference file pinned by commit hash at the top of
> `z-lean/References/Blake3/Spec.lean`."*

Currently empty by design. The trait surface that `References/*` impls
discharge lives in root-level [`Hasher/`](../Hasher) (mirrors
`ark-interop::Compress` / `HashValue` / `VarArityHash` /
`DomainEncoded`).

## Planned subdirectories

```
References/
├── Blake3/Spec.lean       -- Lean port of AONW20 BLAKE3 reference impl.
│                             Discharges Compress<K>, HashValue, VarArityHash
│                             over Digest = Vector UInt8 32.
├── Poseidon/Spec.lean     -- Lean port of Poseidon1 (GKRRS '21).
│                             Discharges Compress<K>, HashValue, VarArityHash
│                             over Digest = F (field element). No preset
│                             ships here — presets land in Presets.lean
│                             alongside their cryptanalytic audit citation.
├── Poseidon/Presets.lean  -- (F, t, R_F, R_P) instance presets, each with
│                             audit citation per upstream Rust convention.
├── Poseidon2/Spec.lean    -- Lean port of Poseidon2 (eprint 2023/323).
└── Poseidon2/Presets.lean
```

## Architectural discipline

* Each `Spec.lean` is the Lean spec for *one* concrete Rust hash
  implementation, pinned by commit hash at the top of the file. The
  Rust impl refines into this Lean spec (via hax extraction +
  refinement theorem); the Lean spec implements the
  [`Hasher/`](../Hasher) traits.

* `References/` files **may not** import anything from consumer crates
  (`VectorCommitment/`, `InteractiveProtocol/`, …) — hashers are
  upstream of all consumers. Only [`Hasher/`](../Hasher) and Mathlib.

* No proof of cryptographic security here. The Lean spec is the
  reference *implementation* — the security analysis (collision
  resistance, indifferentiability, etc.) is documented but axiomatic.

## Status

Empty. Concrete `Blake3/Spec.lean` and friends are independently-scoped
follow-up work — each is 1000+ LOC of Lean against the published
reference, multi-month per hasher. The trait surface in
[`Hasher/`](../Hasher) does **not** block on these landing; the Rust
ark-merkle-commitment crate extracts into `Hasher.Compress`/`HashValue`
opaque-symbol calls in the meantime, with the concrete spec slotting
in whenever the corresponding `References/*/Spec.lean` ships.
