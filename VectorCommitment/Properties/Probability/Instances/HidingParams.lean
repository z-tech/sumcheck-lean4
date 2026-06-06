/-
Copyright (c) 2026 LeanStuff contributors. All rights reserved.
-/
import VectorCommitment.Properties.Probability.Instances.Parameters
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Fintype.BigOperators

/-!
# Hiding parameters and salt-entropy types

The hiding axis is governed by parameters that are *separate* from the binding
digest axis: the per-leaf salt entropy `s`, the message length `ℓ`, the opening
size `Q`, and the random-oracle query budget `q`.  This file names those
parameters and the book's finite-query error expressions, and introduces the
salt-space entropy interface used by the later root-hiding and privacy proofs.

Nothing here reopens a closed binding theorem: the binding capstone
(`Parameters.lean`) is imported only to extend `MerkleHasherParams` with the
salt-width helpers it already carries (`saltElems`, `saltBytes`).
-/

namespace VectorCommitment.Probability

open scoped ENNReal

/-- The parameters a Merkle-commitment hiding bound depends on.  These live on
    the salt/privacy axis and are independent of the binding sizing rule. -/
structure HidingParams where
  /-- digest output bit-length `κ`. -/
  kappa         : Nat
  /-- per-leaf salt entropy `s`. -/
  saltBits      : Nat
  /-- committed message length `ℓ`. -/
  messageLength : Nat
  /-- number of opened positions `Q`. -/
  openingSize   : Nat
  /-- random-oracle query budget `q`. -/
  queryBound    : Nat

namespace HidingParams

/-- Book finite-query **root-hiding** error `ℓ·q / 2^s + ℓ·q / 2^(2κ)`
    (`lemma:mt-root-hiding`): the leaf salt-hit term plus the internal-node
    simulation term. -/
noncomputable def rootHidingError (p : HidingParams) : ENNReal :=
  (p.messageLength * p.queryBound : ENNReal) / 2 ^ p.saltBits
    + (p.messageLength * p.queryBound : ENNReal) / 2 ^ (2 * p.kappa)

/-- Book loose finite-query **privacy** error
    `Q·ℓ·q / 2^s + Q·ℓ·q / 2^(2κ)` (`lemma:mt-privacy`, loose public bound).
    The exact form sums `rootHidingError` over `copath(I) \ path(I)`; this is the
    coarse upper bound downstream IOP/PCP transformations consume. -/
noncomputable def privacyHidingErrorLoose (p : HidingParams) : ENNReal :=
  (p.openingSize * p.messageLength * p.queryBound : ENNReal) / 2 ^ p.saltBits
    + (p.openingSize * p.messageLength * p.queryBound : ENNReal) / 2 ^ (2 * p.kappa)

end HidingParams

/-- A finite salt space carrying at least `saltBits` bits of entropy.  We require
    only a *lower* bound `2 ^ saltBits ≤ |Salt|`, because field-element salts have
    cardinality `|F|^k`, which is generally not a power of two. -/
class SaltEntropy (Salt : Type) [Fintype Salt] where
  /-- the certified entropy `s`. -/
  saltBits : Nat
  /-- the salt space is at least `2^s` large. -/
  card_lower_bound : 2 ^ saltBits ≤ Fintype.card Salt

/-- A salt of `S` bytes. -/
abbrev ByteSalt (S : Nat) := List.Vector (Fin 256) S

/-- A salt of `k` field elements over `F`. -/
abbrev FieldSalt (F : Type) (k : Nat) := List.Vector F k

/-- Byte salts realize exactly `2^(8S)` entropy. -/
theorem byteSalt_card_lower_bound (S : Nat) :
    2 ^ (8 * S) ≤ Fintype.card (ByteSalt S) := by
  have hcard : Fintype.card (ByteSalt S) = 256 ^ S := by
    simp [ByteSalt, card_vector]
  rw [hcard]
  have : (256 : Nat) = 2 ^ 8 := by norm_num
  rw [this, ← pow_mul]

/-- Field salts of `k` elements over a field with at least `2^fieldBits`
    elements realize at least `2^(fieldBits·k)` entropy. -/
theorem fieldSalt_card_lower_bound (F : Type) [Fintype F] (fieldBits k : Nat)
    (hF : 2 ^ fieldBits ≤ Fintype.card F) :
    2 ^ (fieldBits * k) ≤ Fintype.card (FieldSalt F k) := by
  have hcard : Fintype.card (FieldSalt F k) = Fintype.card F ^ k := by
    simp [FieldSalt, card_vector]
  rw [hcard, pow_mul]
  exact Nat.pow_le_pow_left hF k

/-- `SaltEntropy` instance for byte salts (`s = 8S`). -/
instance (S : Nat) : SaltEntropy (ByteSalt S) where
  saltBits := 8 * S
  card_lower_bound := byteSalt_card_lower_bound S

/-- Deterministic salts (`Salt = Unit`) carry zero entropy: `|Unit| = 1 = 2^0`.
    This is the book's `remark:mt-no-privacy` case — a no-op, *not* a weak hiding
    instance, so we record the fact but give `Unit` no positive `SaltEntropy`. -/
theorem unit_card : Fintype.card Unit = 1 := rfl

namespace Instances

open MerkleHasherParams

/-- Field-salt entropy width `s_field = fieldBits · k` carried by the hasher params. -/
def MerkleHasherParams.fieldSaltBits (p : MerkleHasherParams) : Nat :=
  p.fieldBits * p.saltElems

/-- Byte-salt entropy width `s_byte = 8 · S` carried by the hasher params. -/
def MerkleHasherParams.byteSaltBits (p : MerkleHasherParams) : Nat :=
  8 * p.saltBytes

/-- The field-salt entropy target: `λ ≤ fieldBits · k`. -/
def MerkleHasherParams.MeetsFieldSaltTarget (p : MerkleHasherParams) : Prop :=
  p.lam ≤ p.fieldSaltBits

/-- The byte-salt entropy target: `λ ≤ 8 · S`. -/
def MerkleHasherParams.MeetsByteSaltTarget (p : MerkleHasherParams) : Prop :=
  p.lam ≤ p.byteSaltBits

end Instances

end VectorCommitment.Probability
