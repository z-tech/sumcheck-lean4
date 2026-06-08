# `VectorCommitment` — Usage

This doc shows the minimal end-to-end flow for using `VectorCommitment` to
commit, open, and check. The operations below are executable definitions and
the round-trip is checked by `native_decide`.

---

## 1. The demo hasher

A toy, deterministic hasher over `ZMod 65521`. Non-cryptographic by design — the point is that Rust can mirror the arithmetic bit-for-bit.

```lean
import VectorCommitment

open VectorCommitment

def MyHasher : Type := Unit

instance : MerkleHasher MyHasher where
  Symbol      := ZMod 65521
  Digest      := ZMod 65521
  Salt        := Unit
  decEqDigest := inferInstance
  defaultSalt := ⟨()⟩
  hashLeaf    := fun _ x _ => x * 31 + 17
  hashNodes   := fun _ cs => (cs.map id).foldl (fun acc d => acc * 31 + d) 1
```

`Salt := Unit` makes this a non-hiding hasher (see [HIDING.md](HIDING.md)).

---

## 2. The shape

A perfect binary tree with 4 leaves (depth 2):

```lean
def shape : PerfectBinary := PerfectBinary.mk 4
```

---

## 3. The scheme

Bundle the hasher value and the shape into a `MerkleCommitment`:

```lean
def scheme : MerkleCommitment MyHasher PerfectBinary :=
  MerkleCommitment.mk () shape
```

---

## 4. Round-trip

Commit to `[1, 2, 3, 4]`, open at indices `{1, 3}`, check the proof:

```lean
def msg : List (ZMod 65521) := [1, 2, 3, 4]

def committed := scheme.commit msg

def opening := Opening.fromMessageIndices msg [1, 3] |>.toOption.get!

def proof := scheme.open msg committed.snd [1, 3]

lemma roundtrip : scheme.check committed.fst.root opening proof = true := by
  native_decide
```

The `native_decide` discharges the goal by actually running `commit` / `open` / `check` at elaboration time.

---

## 5. Cross-checking against `ark-mt`

To use `VectorCommitment` as a correctness oracle for the Rust crate:

1. On the Rust side, instantiate `MerkleHasher` with the same `x * 31 + 17` (leaf) and `acc * 31 + d` (inner) arithmetic, over a matching modular ring (`ZMod 65521` ↔ a `Fp<65521>` newtype).
2. Run `commit` on `[1, 2, 3, 4]` and `open` at indices `{1, 3}`.
3. Compare:
   - the root digest (`committed.fst.root` in Lean ↔ `commitment.root()` in Rust);
   - the digest list inside the opening proof (`proof` in Lean ↔ `OpeningProof::digests()` in Rust).

If both match exactly, the Rust implementation agrees with the Lean spec on this input.

---

## 6. Current limitations and security proofs

- `commit` / `open` / `check` are real and are exercised by the tests; the demo
  hasher remains intentionally non-cryptographic.
- `HidingVectorCommitment` is a separate typeclass — its hiding commit takes
  explicit typed `Randomness ck` (e.g. a per-leaf salt vector), and `Salt = Unit`
  carries no entropy. See [HIDING.md](HIDING.md).
- ROM position binding is proved over the lazy-sampling oracle, and ROM
  extractability is reduced to the named `cacheExtract_sound` bridge. Hiding is
  the goal-shaped `HasROMHiding` obligation (fixed real/ideal games, fixed error
  `n·q/|Salt| + (n−1)·q/|Digest|²`); it is currently **OPEN** — no instance is
  installed yet, pending the oracle-native commitment game. The honest floor
  (`PerfectHiding` + `not_perfectHiding_singleton`, `PMF.etvDist`, and the
  `2^s ≤ |Salt|` salt-entropy capstones) is proved. See [ROADMAP.md](ROADMAP.md)
  and [INTERFACE.md](INTERFACE.md).
- The lazy-sampling `OracleComp` API mirrors
  [VCVio](https://github.com/Verified-zkEVM/VCV-io), permitting a future
  mechanical dependency swap. z-Lean's direct-induction collision proof remains
  local because it avoids VCVio's eager-seed padding artifact.

---

## 7. For Rust users coming from `ark-mt`

| Rust (`ark-mt`)                    | Lean (`VectorCommitment`)                |
|------------------------------------|----------------------------|
| `MerkleHasher` trait               | `MerkleHasher` typeclass   |
| `MerkleShape` trait                | `MerkleShape` typeclass    |
| `MerkleCommitment<H, S>`           | `MerkleCommitment H S`     |
| `MerkleCommitment::commit(message)`| `scheme.commit msg`        |
| `Opening::from_pairs`              | `Opening.fromPairs`        |
| `OpeningProof<H>`                  | `OpeningProof H`           |
| `CappedMerkleCommitment`           | `CappedMerkleCommitment`   |

Naming convention: Rust `snake_case` becomes Lean `camelCase`; Rust generics `<H, S>` become Lean explicit args `H S`. Otherwise the surface area is intentionally identical so a reader can move between the two crates without re-learning the API.
