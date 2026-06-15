import VectorCommitment.Src.Merkle.Instance
import VectorCommitment.Tests.HasherTests

/-!
# Trait-dispatch round-trip tests

These tests exercise `VectorCommitment.{setup, trim, commit, open, check}`
— the **abstract trait** dispatched through the `MerkleCommitment`
instance — rather than calling the concrete `MerkleCommitment.commit/open/
check` directly (those are covered by `SchemeTests.lean`).

The contract being demonstrated:
* The `VectorCommitment` instance for `MerkleCommitment H S` is
  **computable** end-to-end (no `Classical.ofNonempty`, no `noncomputable`).
* The five trait operations chain into a working round-trip verified by
  `native_decide`.

Hasher: the demo `ZMod 65521` `DemoHasher` from `HasherTests.lean`.
Cryptographically meaningless — its sole purpose here is to exercise the
operational interface end-to-end. The `ark-merkle-commitment` Rust crate's
refinement target is `VectorCommitment.commit/open/check` parametric over
`[MerkleHasher H]`; the production hasher (Blake3 / SHA-256 / Poseidon2)
gets plugged in via the crate's own `MerkleHasher` instance, separate
from this file.
-/

namespace VectorCommitment.Tests.Trait

open MerkleCommitment

-- Concrete commitment instance and `Inhabited` witness so the trait's
-- `setup` (which returns `default`) can synthesize.
def shape4 : PerfectBinary := PerfectBinary.mk 4
def mc4 : MerkleCommitment DemoHasher PerfectBinary := ⟨(), shape4⟩

instance : Inhabited (MerkleCommitment DemoHasher PerfectBinary) := ⟨mc4⟩

-- Trait-level dispatch chain: setup → trim → commit → open → check.
def vcParams :=
  VectorCommitment.setup (V := MerkleCommitment DemoHasher PerfectBinary) 4 2 ⟨0⟩
def vcKeys :=
  VectorCommitment.trim (V := MerkleCommitment DemoHasher PerfectBinary) vcParams 4 2
def vcCk := vcKeys.fst
def vcVk := vcKeys.snd

def msg4 : List (ZMod 65521) := [1, 2, 3, 4]

def vcCommitOut :=
  VectorCommitment.commit (V := MerkleCommitment DemoHasher PerfectBinary) vcCk msg4
def vcCommitment := vcCommitOut.fst
def vcState := vcCommitOut.snd

def queries : List Nat := [0, 2]
def opened : List (ZMod 65521) := [msg4[0]!, msg4[2]!]

def vcProof :=
  VectorCommitment.open (V := MerkleCommitment DemoHasher PerfectBinary)
    vcCk msg4 vcCommitment queries opened vcState

/-- Trait-dispatch round-trip: an honest commit + open verifies under the
    trait's `check`. The reduction goes through the typeclass projection
    chain `VectorCommitment.check → … → MerkleCommitment.check`. -/
lemma trait_roundtrip4 :
    VectorCommitment.check (V := MerkleCommitment DemoHasher PerfectBinary)
      vcVk vcCommitment queries opened vcProof = true := by
  native_decide

/-- Negative test: tampering with a single revealed value flips the
    trait's `check` to `false`. Same `vcProof`, but `opened` lies about
    position 0. -/
def tamperedOpened : List (ZMod 65521) := [msg4[0]! + 1, msg4[2]!]

lemma trait_tampered4_rejected :
    VectorCommitment.check (V := MerkleCommitment DemoHasher PerfectBinary)
      vcVk vcCommitment queries tamperedOpened vcProof = false := by
  native_decide

end VectorCommitment.Tests.Trait
