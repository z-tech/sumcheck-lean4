# Changelog

## 2026-04-21 — Inner-product sumcheck

- Added `Sumcheck/IP/InnerProduct.lean`: `InnerProductStatement` +
  `toSumcheck` reduction to a `SumcheckStatement` on `f * g`;
  `innerProduct_completeness`, `innerProduct_soundness` as corollaries of
  `sumcheck_hasPerfectCompleteness` / `sumcheck_hasSoundnessError`.
- `innerProduct_soundnessError_le_multilinear`: when both factors are
  multilinear, soundness error `≤ n · 2 / |𝔽|` (via
  `maxIndDegree (f * g) ≤ 2`, itself from `degreeOf_mul_le_c`).
- Thin-wrapper form — `f * g` is materialized. A native two-oracle
  protocol (separate prover state for `f` and `g`) is deferred; the
  current form is enough for downstream protocols that build on
  inner-product claims.

## 2026-04-20 — IP Class + #SAT ∈ IP (unconditional) + TQBF scaffold

- Added `InIP` predicate and `IPCertificate` structure
  (`InteractiveProtocol/Properties/IPClass.lean`) with `InIP.mk` and
  `InIP.of_hasProperties` smart constructors; universe-pinned to
  `PublicCoinProtocol.{0,0,0,0}`.
- Added size-indexed analogues: `IPFamilyCertificate`, `InIPFamily`,
  `InIPFamily.mk`, `InIPFamily.of_hasProperties`. Needed because a fixed
  field can't meet `ε ≤ 1/3` for unbounded-size languages — classical IP
  lets the protocol grow with input size.
- **#SAT ∈ IP proved unconditionally** (`Sumcheck/IP/SharpSAT/`):
  - 3-CNF type, `arithmetize`, `sharpSAT_completeness`,
    `sharpSAT_soundness`, `sharpSAT_soundnessError_le` (concrete
    Schwartz–Zippel bound via individual-degree analysis).
  - `sharpSAT_inIPFamily` — conditional on a field scheme with
    `9k² ≤ |F k|` and `ℕ → F k` injective on `[0, 2^k]`.
  - `sharpSAT_inIPFamily_concrete` — discharges both hypotheses with
    `sharpSATField k := ZMod p_k` where `p_k` is a prime
    `≥ max(2^k + 1, 9k² + 1)` selected via `Nat.exists_infinite_primes`.
- TQBF / Shamir scaffolding (`Sumcheck/IP/TQBF/`):
  - `QBF` datatype, `arithmetizeQBF` + correctness vs `boolToField Q.value`.
  - Full multilinear-extension library (`Linearize.lean`): `specialize0`,
    `linearize0`, `linearize_i`, `linearizeAll`, with evaluation and
    individual-degree bounds (`degreeOf_linearizeAll_le_one`).
  - `specialize0_commute` — 0↔1 rename commutes with nested `specialize0`
    (via new `finSuccEquiv_eval_C_eq_aeval` bridge and `aeval`/`rename`
    composition laws).
  - `eval_arithmetizeLeavingFirst` — scalar evaluation collapses to the
    standard quantifier-fold arithmetization.
  - Shamir protocol defined with raw-degree round polynomials; field-size
    hypothesis `3·2^n ≤ |𝔽|`. `tqbf_inIP` still sorry pending honest-round/
    final-check identities (blocked on a `tqbfHonestMessage` cast refactor).
- Test modules: `Sumcheck/Tests/SharpSATTests.lean`,
  `Sumcheck/Tests/TQBFTests.lean`.

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

