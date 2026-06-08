# `VectorCommitment` — Milestone roadmap

This is the Lean equivalent of [`ark-mt/DESIGN.md` §4](https://github.com/arkworks-rs/ark-vc/blob/main/crates/ark-mt/DESIGN.md)'s M0–M10 plan, re-shaped for what's tractable in Lean: no R1CS, fewer parallelism concerns, more proof-driven milestones.

**This branch delivers the operational scheme, deterministic theorem spine, and
the main ROM framework.** Position binding is axiom-clean; ROM extractability
retains one named bridge; hiding is the goal-shaped `HasROMHiding` obligation
with an honest proved floor but no instance yet (OPEN); equivocation is deferred.

**Headline status:** real `commit`/`open`/`check`; a VCVio-compatible
lazy-sampling free monad; a direct-induction birthday bound; axiom-clean ROM
position binding; concrete binding and salt-entropy parameter capstones; and
structural extractability/hiding theorems with the remaining distributional
bridges isolated by name.

**Status:**
- ✅ **L0** — design docs, file tree, build green, demo `ZMod 65521` hasher live.
- ✅ **L1** — real `commit`/`open`/`check` for non-hiding `PerfectBinary`. `SchemeTests.lean` proves `roundtrip4`, `roundtrip8`, and `tampered4_rejected` via `native_decide`. `ShapeTests.lean` pins golden values for `path` / `copath` / `numVertices` on 4- and 8-leaf trees.
- ✅ **L2 done** — `buildLabels` refactored to a pure functional `labelAt`. **Twenty-one real (sorry-free) theorems** in [`Theorems/Completeness.lean`](Properties/Theorems/Completeness.lean), including the universal `mt_completeness` itself:
  1. `labelAt_internal` — recursion equation at internal vertices.
  2. `labelAt_leaf` — recursion equation at leaves.
  3. `combineUp_eq_parent_left` — bridge for left children.
  4. `combineUp_eq_parent_right` — bridge for right children.
  5. `combineUp_at_pos_eq_parent` — parity-agnostic bridge.
  6. `walkCopath_step` — single inductive step of the verifier walk.
  7. `walkCopath_to_root_4_leaf0` — concrete worked example for size 4.
  8. `walkCopath_lifts_labelAt` — **the universal walk-to-root induction**, the heart of the completeness proof.
  9. `mt_completeness_empty` — empty-opening case.
  10. `commit_root_eq_labelAt_zero` — bridge from imperative `commit` root to functional `labelAt 0`.
  11. `trapdoor_labels_eq_labelAt` — bridge from trapdoor's stored labels to `labelAt`.
  12. `ancestor_bounds_pow2` — induction on path length: `2^(d-k) ≤ ancestor pos k + 1 ≤ 2^(d-k+1) - 1`.
  13. `ancestor_succ_eq` — `ancestor pos (k+1) = (ancestor pos k - 1) / 2`.
  14. `ancestor_chain_precondition` — every ancestor along the leaf-to-root path is a valid internal vertex.
  15. `ancestor_at_depth_eq_zero` — the `d`-th ancestor of any leaf is the root.
  16. `copathOf_go_eq_map_siblingOf_ancestor` — structural identity on the `copathOf.go` recursion.
  17. `copath_eq_siblingOf_ancestor` — `MerkleShape.copath i` matches `(List.range d).map (siblingOf ∘ ancestor)`.
  18. `ancestor_lt_total`, `siblingOf_ancestor_lt_total` — vertex bounds on the ancestor chain.
  19. `reconstruct_eq_root` — **per-leaf completeness**: for an honest opening of a single leaf, the reconstructed digest equals `labelAt mc msg salts 0`.
  20. `perfectBinary_depth_eq_of_pow2`, `perfectBinary_numLeaves_eq_pow2_depth` — depth/numLeaves identities for power-of-2 `PerfectBinary`.

  The universal `mt_completeness` is closed via a `check_forIn_eq_true` helper that reduces the `Id.run do for ... return true` loop body to per-triple equality checks, then chains `commit_root_eq_labelAt_zero` with `reconstruct_eq_root`.

- ✅ **L3 done** — five Option-B (binding-form / contrapositive) collision lemmas + the multi-leaf `mt_colliding_paths_binding` and the `check_iff` multi-leaf bridge in [`Lemmas/CollisionLemma.lean`](Properties/Lemmas/CollisionLemma.lean).
- ✅ **L5 done** — `mt_binding` and `mt_other_binding` are proven in [`Theorems/Binding.lean`](Properties/Theorems/Binding.lean); [`Instances/BindingROM.lean`](Properties/Probability/Instances/BindingROM.lean) closes the shared-lazy-oracle position-binding game with `binding_win_le_trace_collision` and the proved birthday bound.
- ✅ **L6 done** — `deriveVertexSet` body, `path_pruning_is_copaths_minus_paths`, and `opening_proof_size_bound` (`|deriveVertexSet I| ≤ |copath(I)|`).
- ◯ **L8 Hiding OPEN — goal-shaped obligation + honest floor landed.** Hiding is the goal-shaped `HasROMHiding` obligation: fixed real/ideal games and a fixed error `n·q/|Salt| + (n−1)·q/|Digest|²`, no configurable advantage field. The proved floor is the structural `mt_root_hiding` / `mt_root_hiding_commit` backbone, operational per-leaf salts, `HidingParams`, salt-space bounds and field/byte salt-entropy capstones, `PMF.etvDist`, and `PerfectHiding` with its `not_perfectHiding_singleton` negative result. **No `HasROMHiding` instance is installed yet**: the honest real game is the oracle-native commitment distribution (sampling the oracle lazily), and its construction plus the basic-commitment → root-hiding → selective-opening privacy reduction are the remaining work. The staged plan: (1) port the `PMF` total-variation / lazy-cache query-handler / identical-until-bad foundation; (2) basic-commitment hiding `q/|Salt|`; (3) oracle-native Merkle commitment + bottom-up root hiding; (4) selective-opening privacy simulator + `Q·n·q` loose bound; (5) install the `HasROMHiding` instance.
- 🟨 **Extractability reduced to one ROM bridge** — deterministic `mt_extractability` and `mt_multi_extractability` are proved. The shared-oracle instance is implemented and reduced to `extraction_win_le_trace_collision`, whose remaining work is the documented `cacheExtract_sound` bridge.
- ⏳ **Equivocation** (book §12.7) — deferred; it requires programmable-RO simulator machinery.
- ✅ **ROM collision and binding spine** — the lazy-sampling `OracleComp` model, direct-induction `run_coll_le`, `coupling_trace_le_collisionBound`, Merkle trace-collision reductions, `checkOracle` acceptance lemmas, and ROM position-binding instance are proved.
- ✅ **PathCopath.lean** — three real proven lemmas: `copath_length_eq_depth`, `path_length_eq_depth_succ` (corrected from off-by-one), `deriveVertexSet_subset_internal`. Useful structural facts about the heap-indexed perfect binary tree.
- ✅ **Parameters** — `MerkleHasherParams.ofField` computes digest and salt widths; the binding target and field/byte salt-entropy targets are proved, with BabyBear binding and hiding capstones.
- ✅ **L4** — [`Properties/Probability/RandomOracle.lean`](Properties/Probability/RandomOracle.lean) retains the legacy `RODistribution := PMF.pure` only for downstream compatibility. Real probabilistic arguments use the lazy-sampling `OracleComp` / `QueryLog` model. Its structural API mirrors [VCVio](https://github.com/Verified-zkEVM/VCV-io); z-Lean intentionally keeps its own direct-induction coupling proof rather than VCVio's eager-seed/padding route.
- 🟨 **L9 (partial)** — `PerfectKAry k` and `ArbitraryLength` shapes have real `MerkleShape` instance bodies in [`Src/Merkle/Shape.lean`](Src/Merkle/Shape.lean), mirroring the Rust `crates/ark-mt/src/shape.rs` algorithms (heap-indexed for `PerfectKAry`; precomputed parent/children vectors via ceil/floor split for `ArbitraryLength`). [`Tests/ShapeTests.lean`](Tests/ShapeTests.lean) pins golden values for `PerfectKAry 4` (16 leaves) and `ArbitraryLength.mk 7`. Remaining for full L9: wire the new shapes into `MerkleCommitment.commit`/`open`/`check` (currently specialised to `PerfectBinary`-style heap arithmetic in `buildLabels`).
- ✅ **Instance.lean wired** — `instance : VectorCommitment (MerkleCommitment H S)` is now real (no `sorry`) in [`Src/Merkle/Instance.lean`](Src/Merkle/Instance.lean). `UniversalParams := MerkleCommitment H S`, `CommitterKey = VerifierKey = MerkleCommitment H S`. The trait-level `setup`/`trim`/`commit`/`open`/`check` delegate to the concrete Merkle bodies.
- ✅ **L10 partial: Capped commitments** — [`Src/Merkle/Capped.lean`](Src/Merkle/Capped.lean) ships real `commit`/`open`/`check` for `CappedMerkleCommitment`. Cap of height `c` produces a `List Digest` of length `|verticesAtLayer c|`, opening proofs are truncated by `c` levels, and `check` walks the truncated copath then matches the layer-`c` ancestor against the supplied cap entry. Four `native_decide` round-trip tests: `roundtrip4_h0`, `roundtrip4_h1`, `roundtrip4_h2` (cap heights 0, 1, 2 over 4 leaves), and `roundtrip8_h2` (8 leaves, cap height 2).

---

## 1. Milestones

| Milestone | Deliverable | Verification |
|---|---|---|
| **L0** | Skeleton: typeclasses, data types, and `sorry`'d theorem statements for every book result in §12 + §20 + §12.7. Four design docs (DESIGN, HIDING, ROADMAP, USAGE). All file homes from [DESIGN.md §2](DESIGN.md#2-module-layout) exist. The demo `ZMod 65521` hasher is wired into `HasherTests.lean` only — `commit`/`open`/`check` bodies remain `sorry`. | `lake build` of `«VectorCommitment»` passes. Every lemma/theorem typechecks modulo `sorry`. One smoke `lemma` on the empty/size-0 round-trip compiles via `native_decide`. |
| **L1** | Concrete bodies for `commit` / `open` / `check` on the non-hiding `PerfectBinary` shape with the demo hasher. `OpeningProof` becomes a real structure, not `sorry`. `instance : VectorCommitment (MerkleCommitment H PerfectBinary)` glue lands in `Merkle/Instance.lean`. Test vectors from the Rust crate's `tests/scheme.rs` get pinned as `lemma … := by native_decide`. | `SchemeTests.lean` round-trip on 4, 8, 16 leaves. Outputs match a Rust-side test vector (to be supplied alongside this milestone). `TraitTests.lean` confirms the `VectorCommitment` instance resolves. |
| **L2** | Prove `lemma:mt-completeness` (book §12.2). Combinatorial — no probability needed; structural induction on tree depth + `path`/`copath` algebra. | `Theorems/Completeness.lean` is `sorry`-free. `#print axioms mt_completeness` lists no `sorryAx`. |
| **L3** | Prove `lemma:simple-mt-colliding-paths` and `lemma:mt-colliding-paths` (book §12.3). Combinatorial; sets up the binding proof. Builds on `Lemmas/PathCopath.lean` (also closed at this milestone). | `Lemmas/CollisionLemma.lean` and `Lemmas/PathCopath.lean` are `sorry`-free. |
| **L4** | Stand up the lazy-sampling `OracleComp` / `QueryLog` random-oracle model, with a VCVio-compatible structural API and PMF interpreter. Keep the function-view `RODistribution` only as a legacy compatibility layer. | `RandomOracle.lean` compiles; `run_bind` and the direct-induction `coupling_trace_le_collisionBound` are proved. |
| **L5** | Prove `lemma:mt-binding` (§12.4), lift it to the shared lazy-oracle game, and derive concrete parameter bounds. | `Theorems/Binding.lean`, `Instances/BindingROM.lean`, and the binding capstones in `Instances/Parameters.lean` are proved. |
| **L6** | Path pruning. Implement `deriveVertexSet` in `Scheme.lean` with a real body and prove `lemma:path-pruning-is-copaths-minus-paths` plus the size bound from book Eq. 20.x. Adapt `open` / `check` to use the pruned vertex set; existing L1 test vectors must still pass. | `Lemmas/PathPruning.lean` is `sorry`-free. `SchemeTests.lean` opening-proof size measurably shrinks for 2+ indices and matches the book's bound. |
| **L7** | Hiding salt path. Instantiate `Salt := Vector (Fin 256) 16` (or similar) on a hiding variant of the demo hasher and provide `instance : HidingVectorCommitment (MerkleCommitment H S)` for `H.Salt ≠ Unit`. The compile-time rejection promised in [HIDING.md](HIDING.md) starts biting: callsites with hiding bounds reject the non-hiding hasher. | New `SchemeTests` cases for the hiding hasher round-trip. A negative test confirms `[HidingVectorCommitment …]` fails to resolve for `H.Salt = Unit`. |
| **L8** | Declare the goal-shaped `HasROMHiding` obligation, prove structural root hiding, operational salt support, salt-entropy parameters, and the honest floor; then close ROM hiding/privacy over the lazy-sampling model. | Structural hiding, the `HasROMHiding` declaration, parameter capstones, and the floor (`PMF.etvDist`, `PerfectHiding` + `not_perfectHiding_singleton`) are proved. The oracle-native commitment game and the root-hiding/privacy bounds are the remaining work; no `HasROMHiding` instance is installed yet. |
| **L9** | `PerfectKAry k` and `ArbitraryLength` shapes wired through the scheme. Same `commit`/`open`/`check` code path; only `MerkleShape` instance changes. The `if h : k = 2` binary fast-path stays available. | `ShapeTests.lean` becomes parametric over shape. Round-trips at `k = 2, 3, 4` and at `numLeaves ∈ {7, 13, 17}` for `ArbitraryLength`. |
| **L10** | Optional capabilities: `CappedMerkleCommitment` plus `LocallyUpdatable`, `LeavesAccessible`, `Equivocable` instances. The `Equivocable` *instance* lands; the `lemma:mt-equivocation` *theorem* statement stays in place but its proof remains `sorry` (deep §12.7 argument, deferred indefinitely). | One round-trip test per capability under `Tests/`. `#print axioms` on the equivocation theorem still reports `sorryAx` — flagged in `Theorems/Equivocation.lean` as known and intentional. |

---

## 2. L0 acceptance criteria

L0 is done iff all of the following hold:

1. The four design docs exist: `VectorCommitment/DESIGN.md`, `VectorCommitment/HIDING.md`, `VectorCommitment/ROADMAP.md`, `VectorCommitment/USAGE.md`.
2. Every file path listed in [DESIGN.md §2](DESIGN.md#2-module-layout) exists (modulo placeholder bodies).
3. `lakefile.lean` contains `lean_lib «VectorCommitment» where`.
4. `lake build` succeeds with no errors and no warnings beyond `declaration uses 'sorry'`.
5. Every `class`, `structure`, `def`, `lemma`, and `theorem` declared in §1's Lean homes typechecks. `theorem`s may have body `:= sorry`; statements must be well-formed.
6. One smoke test passes via `native_decide` — the size-0 round-trip (`commit []` followed by `check` on the empty index list) lives in `SchemeTests.lean` and closes with a `by native_decide` proof. This forces enough of the data-structure layer to be `def` rather than `noncomputable`.

---

## 3. Critical-path decision points

- **L1 success determines whether the typeclass shape is right.** If wiring up the demo hasher to `commit`/`open`/`check` against the L0 typeclass surface requires bizarre workarounds (e.g. extra associated types, `noncomputable` leaks into `Src/`, `DecidableEq` instances that won't synthesize), revise [DESIGN.md §3.1–§3.3](DESIGN.md#31-merklehasher-is-one-typeclass-with-an-associated-salt-type) **before** continuing to L2. Sunk-cost on `sorry`'d theorems against a wrong surface is cheap to abandon; sunk-cost after L2 is not.
- **L4 selected the lazy-sampling RO shape.** [DESIGN.md §3.5](DESIGN.md#35-random-oracle-infrastructure-in-propertiesprobabilityrandomoraclelean) records the VCVio-compatible free-monad structure and z-Lean's direct-induction coupling proof. The legacy function-view `RODistribution` is not the model used by the ROM security reductions.
- **L6 path pruning may force `Scheme.lean` refactors.** The L1 implementation is allowed to be naive (one full path per index). If pruning at L6 requires changing the `OpeningProof` representation, the L1 test vectors get re-pinned — flag this in the L6 PR rather than silently rewriting them.

---

## 4. Out of roadmap

- **R1CS gadgets.** Lean has no R1CS DSL and no path to one. The Rust crate's `gadget.rs` has no Lean home and no milestone.
- **Parallel `commit`.** Lean has no rayon. Single-threaded performance is sufficient — `VectorCommitment` is an oracle for small examples, not a production prover.
- **Byte-level wire-format compatibility with `ark-serialize`.** `VectorCommitment` cross-checks Rust output by *value* (digest equality on small tests), not by byte stream. If wire compatibility ever matters, a `WireEncode` typeclass lands as a separate module — not a milestone.
- **Production hashers (Poseidon2, Blake3).** Demo `ZMod 65521` hasher is the only one shipped. Real hashers are user-supplied; the typeclass surface guarantees they slot in without scheme-level changes.
- **Verified compilation to Rust.** `VectorCommitment` is a spec, not a code generator.
