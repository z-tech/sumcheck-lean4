/-
Copyright (c) 2026 LeanStuff contributors. All rights reserved.
-/
import VectorCommitment.Properties.Probability.HiddenQuery
import VectorCommitment.Properties.Probability.HidingSaltPath
import VectorCommitment.Properties.Probability.ROHasher
import VectorCommitment.Properties.Theorems.Hiding

/-!
# ROM Merkle root hiding

This file formalizes the book's finite-query Merkle root-hiding theorem
(`lemma:mt-root-hiding`): the commit-root distribution, taken over fresh uniform
per-leaf salts, is `rootHidingError`-close to a uniform digest.

```text
rootHidingError p = ℓ·q / 2^s + ℓ·q / 2^(2κ)
```

The first term is the leaf salt-hit error (one `hidden_query_hit_le` per leaf,
union-bounded over `ℓ` leaves); the second is the internal-node simulation error
(each internal node is a basic commitment with `2κ`-bit "salt"), and the
structural backbone is the proved `mt_root_hiding` lemma — the message can reach
the root only through the leaf hashes.

The distributional hybrid that glues these together is the one named gap
(`mt_root_hiding_rom_bound`), whose statement matches the book lemma exactly.
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

/-- **Merkle root hiding in the ROM (book `lemma:mt-root-hiding`).**  The real
    root distribution and the simulated uniform root are `rootHidingError p`-close
    in total-variation distance, for a `q`-query distinguisher.

    *Isolated distributional core.*  Proof decomposition (book):
    1. leaf layer — replace each `H(mᵢ, saltᵢ)` by a uniform digest; one
       `hidden_query_hit_le` per leaf, union-bounded over `ℓ = messageLength`;
    2. internal layers — replace each internal-node hash by a uniform digest,
       charged `q / 2^(2κ)` per node via `cm-hiding` at `2κ`-bit salt;
    3. structural propagation — `mt_root_hiding` shows the message reaches the
       root only through leaf hashes.
    The hybrid that sums these into a TV bound is the single named gap, matching
    the book statement. -/
theorem mt_root_hiding_rom_bound {S : Type} [MerkleShape S]
    (mc : MerkleCommitment (ROHasher.ROHasherValue κ) S)
    (msg : List (MerkleHasher.Symbol (ROHasher.ROHasherValue κ)))
    (p : HidingParams) (q : Nat)
    (hκ : p.kappa = κ) (hℓ : p.messageLength = msg.length) (hq : p.queryBound = q)
    (E : Set (List.Vector Bool κ)) :
    (realRootDist mc msg).toOuterMeasure E
      ≤ (rootSimulator κ).toOuterMeasure E + p.rootHidingError := by
  -- One-sided event indistinguishability: the real root is no more likely to land
  -- in any event `E` than the uniform simulated root, up to `rootHidingError`.
  -- (Taking the sup over `E` gives the TV-distance form.) Structural content via
  -- `mt_root_hiding`; the distributional hybrid is the named gap.
  sorry

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
