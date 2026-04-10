# Changelog

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

