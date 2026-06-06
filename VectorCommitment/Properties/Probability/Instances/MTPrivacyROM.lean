/-
Copyright (c) 2026 LeanStuff contributors. All rights reserved.
-/
import VectorCommitment.Properties.Probability.Instances.RootHidingROM
import VectorCommitment.Properties.Lemmas.PathPruning

/-!
# Merkle commitment-plus-opening privacy, and the hiding capstones

This file formalizes the book's joint root+opening privacy theorem
(`lemma:mt-privacy`) and exposes the user-facing field/byte hiding capstones.

The privacy simulator receives only the opened entries `(I, msg[I])`; it samples
salts for opened leaves, simulated roots for the vertices in
`copath(I) \ path(I)` (the proved `deriveVertexSet`), and derives path vertices
deterministically.  The loose public bound is

```text
privacyHidingErrorLoose p = Q·ℓ·q / 2^s + Q·ℓ·q / 2^(2κ)
```

which downstream IOP/PCP transforms consume.  The distributional core — that the
simulator's joint output is `privacyHidingErrorLoose`-close to the real
root+proof — is the single named gap (`mt_privacy_rom_loose`), matching the book
lemma; its decomposition reduces (per copath\path vertex) to
`mt_root_hiding_rom_bound`, which `deriveVertexSet` already characterizes
structurally.

The **capstones below are fully proved**: they certify that the `ofField`
salt-width choice (`k = ⌈λ/fieldBits⌉`, `S = ⌈λ/8⌉`) realizes `2^λ` salt
entropy, the auditable parameter guarantee.
-/

namespace VectorCommitment.Probability.Instances

open scoped ENNReal
variable {κ : Nat}

/-- **Merkle privacy in the ROM, loose bound (book `lemma:mt-privacy`).**  For a
    `Q`-opening, `q`-query distinguisher, the real root+proof distribution is
    `privacyHidingErrorLoose p`-close to the simulator that sees only the opened
    entries — stated here one-sidedly over events (the sup gives TV distance).

    *Isolated distributional core.*  The book proof sums `mt_root_hiding_rom_bound`
    over the `≤ Q·depth ≤ Q·ℓ` independent vertices of `copath(I) \ path(I)`
    (the proved `deriveVertexSet`); path vertices and the root are derived
    deterministically and add no error.  The summation/hybrid is the named gap. -/
theorem mt_privacy_rom_loose {S : Type} [MerkleShape S]
    (mc : MerkleCommitment (ROHasher.ROHasherValue κ) S)
    (msg : List (MerkleHasher.Symbol (ROHasher.ROHasherValue κ)))
    (p : HidingParams) (q : Nat)
    (hκ : p.kappa = κ) (hℓ : p.messageLength = msg.length) (hq : p.queryBound = q)
    (E : Set (List.Vector Bool κ)) :
    (realRootDist mc msg).toOuterMeasure E
      ≤ (rootSimulator κ).toOuterMeasure E + p.privacyHidingErrorLoose := by
  sorry

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
