/-
Copyright (c) 2026 LeanStuff contributors. All rights reserved.
-/
import VectorCommitment.Src.Security.Hiding
import VectorCommitment.Src.Merkle.Instance
import VectorCommitment.Properties.Probability.ROHasher

/-!
# ROM hiding for RO-derived Merkle commitments — OPEN

The goal-shaped hiding obligation is `HasROMHiding`
(`VectorCommitment/Src/Security/Hiding.lean`): a finite-query ROM hiding bound
stated against fixed real/ideal games and a fixed error
`n·q / |Salt| + (n−1)·q / |Digest|²`. It supersedes the former generic
`HasHiding`, whose ROM instance measured a *collision* advantage (trace-collision
probability bounded by `collisionBound κ q`) that does not capture an adversary
distinguishing two committed messages.

**No `HasROMHiding` instance is installed for the Merkle scheme yet.** The honest
real game is the oracle-native commitment-root distribution, sampling the oracle
lazily rather than against a fixed oracle; its construction and the bottom-up
root-hiding hybrid are the remaining work. A fixed-oracle real game would be
false and a `real = ideal` placeholder vacuous, so hiding is reported **OPEN**
until the real proof lands. See `VectorCommitment/ROADMAP.md` for the staged plan
(basic-commitment hiding → root-hiding hybrid → selective-opening privacy).

The honest, fully-proved floor lives in:
  * `VectorCommitment/Src/Security/Hiding.lean` — `PerfectHiding`,
    `not_perfectHiding_singleton`, `PMF.etvDist`;
  * `HidingParams.lean` / `*_salt_card_ge_lam` — the `2 ^ s ≤ |Salt|` salt
    arithmetic certificates.
-/
