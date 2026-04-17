# Changelog

## 2026-04-17 — Canonical Cleanup & eval Migration

- Removed `Adversary` def; `sumcheckProtocol` now uses `Prover` directly
- Removed `AdversaryTranscript` def; replaced by `proverTranscript`
- Slimmed `Transcript` struct: removed `claims` field (now computed on the fly)
- Unified probability definitions: `probEvent` + `allChallenges` live in `InteractiveProtocol`
- Migrated `eval₂ (RingHom.id 𝔽)` to `eval` across ~185 call sites
- Removed `@HAdd.hAdd _ _ _ instHAdd` / `@HMul.hMul` workarounds; now plain `+` and `*` (enabled by CompPoly fork: Verified-zkEVM/CompPoly#192)
- Canonicalized casing across the repo to match Lean/Mathlib conventions
- Bumped mathlib `v4.26.0` → `v4.28.0`

## 2026-04-09 — Interactive Protocol Interface & Refactor

- Generic `PublicCoinProtocol` interface with Fiat-Shamir transformation

## 2026-02-06 — Soundness & Completeness Proved

- `perfect_completeness`: honest prover accepted with probability 1
- `soundness_dishonest`: dishonest claim accepted with probability at most n * d / |F|

## 2025-12-21 — Switch to CMvPolynomial

- Adopted zkEVM `CompPoly` library for computable multivariate polynomials

## 2026-01-02 — End-to-End Sumcheck

- Complete sumcheck implementation over `CMvPolynomial` with computable transcripts
- Prover, verifier, and test suite over concrete fields (ZMod 19)

