/-
Copyright (c) 2026 LeanStuff contributors. All rights reserved.
-/
import VectorCommitment.Properties.Probability.Instances.RootHidingROM
import VectorCommitment.Properties.Lemmas.PathPruning

/-!
# Merkle commitment-plus-opening privacy capstones — privacy theorem OPEN

The book's joint root+opening privacy theorem (`lemma:mt-privacy`) is the
`HasROMHiding.privacyError` obligation; the loose public bound it targets is

```text
privacyHidingErrorLoose p = Q·ℓ·q / 2^s + Q·ℓ·q / 2^(2κ)
```

The honest privacy statement is the `HasROMHiding.privacyError` obligation: the
real (commitment, opening) view is `privacyError`-close to a simulator that sees
only the opened entries `(I, msg[I])`, samples salts for opened leaves, samples
simulated roots for the vertices in `copath(I) \ path(I)` (the proved
`deriveVertexSet`), and derives path vertices deterministically. A bound over
roots alone would not be a privacy statement (it carries no opening proof and no
selective-opening simulator); the simulator and its bound are the remaining work
(see `ROADMAP.md`). The combinatorial core (`deriveVertexSet = copath(I) \
path(I)`) is the `PathPruning` scaffolding.

The **capstones below are fully proved**: they certify that the `ofField`
salt-width choice (`k = ⌈λ/fieldBits⌉`, `S = ⌈λ/8⌉`) realizes `2^λ` salt
entropy, the auditable parameter guarantee.
-/

namespace VectorCommitment.Probability.Instances

open scoped ENNReal
variable {κ : Nat}

/-! ## Hiding capstones (fully proved)

These instantiate the salt-entropy lemmas at the concrete `babyBear` parameter
constructor, giving zero-hypothesis-on-the-construction guarantees that the
chosen salt widths certify `2^λ` entropy. -/

/-- **BabyBear byte-salt hiding capstone (proved).**  `S = ⌈λ/8⌉` byte salts
    realize at least `2^λ` entropy — no construction hypothesis needed. -/
theorem babyBear_byte_salt_hiding (lam qBits : Nat) :
    2 ^ lam ≤ Fintype.card (ByteSalt (MerkleHasherParams.babyBear lam qBits).saltBytes) :=
  byte_salt_card_ge_lam (MerkleHasherParams.babyBear lam qBits)
    (meetsByteSaltTarget_ofField 30 lam qBits)

/-- **BabyBear field-salt hiding capstone (proved).**  Over a field with at least
    `2^30` elements, `k = ⌈λ/30⌉` field-element salts realize at least `2^λ`
    entropy. -/
theorem babyBear_field_salt_hiding (F : Type) [Fintype F] (lam qBits : Nat)
    (hF : 2 ^ 30 ≤ Fintype.card F) :
    2 ^ lam ≤
      Fintype.card (FieldSalt F (MerkleHasherParams.babyBear lam qBits).saltElems) :=
  field_salt_card_ge_lam F (MerkleHasherParams.babyBear lam qBits) hF
    (meetsFieldSaltTarget_ofField 30 lam qBits (by norm_num))

end VectorCommitment.Probability.Instances
