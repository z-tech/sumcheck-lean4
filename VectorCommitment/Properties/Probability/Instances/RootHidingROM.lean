/-
Copyright (c) 2026 LeanStuff contributors. All rights reserved.
-/
import VectorCommitment.Properties.Probability.HiddenQuery
import VectorCommitment.Properties.Probability.HidingSaltPath
import VectorCommitment.Properties.Probability.ROHasher
import VectorCommitment.Properties.Theorems.Hiding

/-!
# ROM Merkle root hiding — root-hiding theorem OPEN; salt arithmetic proved

The book's finite-query Merkle root-hiding theorem (`lemma:mt-root-hiding`) — the
oracle-native commit-root distribution is `rootHidingError`-close to a uniform
digest — is the `HasROMHiding.rootError` obligation, with

```text
rootHidingError p = ℓ·q / 2^s + ℓ·q / 2^(2κ)
```

the leaf salt-hit error plus the internal-node simulation error. Its structural
backbone is the proved `mt_root_hiding` lemma (the message reaches the root only
through the leaf hashes).

The honest real game must sample the oracle: the root distribution is taken over
both the fresh per-leaf salts **and** the lazily-sampled oracle. Stating the
bound against a single *fixed* oracle would be false — for an arbitrary fixed
`H(m, ·)` the root over uniform salt need not be close to uniform — so the
oracle-sampling game and the bottom-up hybrid are the remaining work
(see `ROADMAP.md`).

The salt-entropy *target* lemmas below are fully proved and are the parameter
layer the field/byte capstones consume.
-/

namespace VectorCommitment.Probability.Instances

open scoped ENNReal
variable {κ : Nat}

/-- The root simulator outputs a uniform `κ`-bit digest (book `MTRootSimulator`). -/
noncomputable def rootSimulator (κ : Nat) : PMF (List.Vector Bool κ) :=
  PMF.uniformOfFintype _

/-- The real root distribution: commit to `msg` with fresh uniform per-leaf
    salts and read off the root. -/
noncomputable def realRootDist {S : Type} [MerkleShape S]
    (mc : MerkleCommitment (ROHasher.ROHasherValue κ) S)
    (msg : List (MerkleHasher.Symbol (ROHasher.ROHasherValue κ))) :
    PMF (List.Vector Bool κ) :=
  haveI : Fintype (MerkleHasher.Salt (ROHasher.ROHasherValue κ)) :=
    inferInstanceAs (Fintype (List.Vector Bool κ))
  haveI : Nonempty (MerkleHasher.Salt (ROHasher.ROHasherValue κ)) :=
    inferInstanceAs (Nonempty (List.Vector Bool κ))
  (mc.commitWithUniformSalts msg).map (fun p => p.1.root)

/-! `realRootDist` is the fixed-oracle real distribution and `rootSimulator` the
uniform simulator; they are the honest scaffolding the oracle-sampling
`HasROMHiding.rootRealGame` and its bound build on. -/

/-! ## Salt-entropy target lemmas (fully proved)

These discharge the `MeetsFieldSaltTarget` / `MeetsByteSaltTarget` predicates for
`MerkleHasherParams.ofField`-constructed parameters, and convert them into the `2^λ ≤ |Salt|`
entropy facts the privacy capstones need.  They are the salt-axis analogue of the
binding capstone's `meetsBindingTarget_ofField`. -/

/-- `MerkleHasherParams.ofField` always meets the field-salt entropy target: `λ ≤ fieldBits·k`. -/
theorem meetsFieldSaltTarget_ofField (fieldBits lam qBits : Nat) (hfb : 0 < fieldBits) :
    (MerkleHasherParams.ofField fieldBits lam qBits).MeetsFieldSaltTarget := by
  show lam ≤ (MerkleHasherParams.ofField fieldBits lam qBits).fieldSaltBits
  show lam ≤ fieldBits * (MerkleHasherParams.ofField fieldBits lam qBits).saltElems
  -- saltElems = ⌈lam / fieldBits⌉, so fieldBits · saltElems ≥ lam by `le_mul_ceilDiv`.
  exact le_mul_ceilDiv lam fieldBits hfb

/-- `MerkleHasherParams.ofField` always meets the byte-salt entropy target: `λ ≤ 8·S`. -/
theorem meetsByteSaltTarget_ofField (fieldBits lam qBits : Nat) :
    (MerkleHasherParams.ofField fieldBits lam qBits).MeetsByteSaltTarget := by
  show lam ≤ (MerkleHasherParams.ofField fieldBits lam qBits).byteSaltBits
  show lam ≤ 8 * (MerkleHasherParams.ofField fieldBits lam qBits).saltBytes
  -- saltBytes = ⌈lam / 8⌉, so 8 · saltBytes ≥ lam.
  exact le_mul_ceilDiv lam 8 (by norm_num)

/-- **Field-salt capstone (proved).**  A field with at least `2^fieldBits`
    elements gives `k = ⌈λ/fieldBits⌉` field-element salts at least `2^λ` large. -/
theorem field_salt_card_ge_lam (F : Type) [Fintype F] (p : MerkleHasherParams)
    (hF : 2 ^ p.fieldBits ≤ Fintype.card F) (htgt : p.MeetsFieldSaltTarget) :
    2 ^ p.lam ≤ Fintype.card (FieldSalt F p.saltElems) := by
  calc 2 ^ p.lam
      ≤ 2 ^ (p.fieldBits * p.saltElems) := Nat.pow_le_pow_right (by norm_num) htgt
    _ ≤ Fintype.card (FieldSalt F p.saltElems) :=
        fieldSalt_card_lower_bound F p.fieldBits p.saltElems hF

/-- **Byte-salt capstone (proved).**  `S = ⌈λ/8⌉` byte salts are at least `2^λ` large. -/
theorem byte_salt_card_ge_lam (p : MerkleHasherParams) (htgt : p.MeetsByteSaltTarget) :
    2 ^ p.lam ≤ Fintype.card (ByteSalt p.saltBytes) := by
  calc 2 ^ p.lam
      ≤ 2 ^ (8 * p.saltBytes) := Nat.pow_le_pow_right (by norm_num) htgt
    _ ≤ Fintype.card (ByteSalt p.saltBytes) := byteSalt_card_lower_bound p.saltBytes

end VectorCommitment.Probability.Instances
