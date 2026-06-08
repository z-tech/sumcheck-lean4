/-
Copyright (c) 2026 LeanStuff contributors. All rights reserved.
-/
import VectorCommitment.Properties.Probability.Instances.BindingROM
import Mathlib.Data.ENNReal.Basic

/-!
# Hasher instantiation capstone

Choose a field, a security level `λ`, and a query budget `q_H`;
get back a machine-checked theorem that the resulting Merkle commitment
is `λ`-bit position binding.

## The chain

```
Pr[binding failure]
  ≤ Pr[trace collision]        [binding_win_le_trace_collision,  BindingROM]
  ≤ collisionBound κ q         [coupling_trace_le_collisionBound, Coupling]
  ≤ 2^(-λ)                    [collisionBound_le_inv_pow,        THIS FILE]
```

The three layers combine in `instantiation_binding_secure`. `babyBear_binding_secure`
is the one-liner specialization that puts concrete BabyBear/KoalaBear/M31 numbers in.
-/

open VectorCommitment.Probability

namespace VectorCommitment.Probability.Instances

open scoped ENNReal

/-- Ceiling division: `ceilDiv a b = ⌈a / b⌉` (with convention `ceilDiv a 0 = 0`). -/
def ceilDiv (a b : Nat) : Nat := (a + b - 1) / b

theorem le_mul_ceilDiv (a b : Nat) (hb : 0 < b) : a ≤ b * ceilDiv a b := by
  unfold ceilDiv
  have hdm := Nat.div_add_mod (a + b - 1) b
  have hmod := Nat.mod_lt (a + b - 1) hb
  omega

/-- The parameter record a developer selects when choosing a hasher.
    Fields correspond one-to-one with the audit slide symbols. -/
structure MerkleHasherParams where
  fieldBits   : Nat  -- ⌊log₂ |F|⌋ — conservative field-element bit count
  digestElems : Nat  -- D — field elements per digest
  saltElems   : Nat  -- k — field elements for per-leaf salt (hiding axis)
  saltBytes   : Nat  -- S — bytes for per-leaf salt in byte-oriented hashers
  lam         : Nat  -- λ — target security level in bits
  qBits       : Nat  -- q_H — query budget exponent (≤ 2^q_H queries)

namespace MerkleHasherParams

/-- Realized digest bit-length: κ = fieldBits × digestElems. -/
def kappa (p : MerkleHasherParams) : Nat := p.fieldBits * p.digestElems

/-- The standalone-binding sizing rule: the digest must absorb λ + 1 + 2·q_H bits of slack.
    Decidable, so it can be checked by `native_decide` for any concrete parameters. -/
def MeetsBindingTarget (p : MerkleHasherParams) : Prop :=
  p.lam + 1 + 2 * p.qBits ≤ p.kappa

instance (p : MerkleHasherParams) : Decidable (MeetsBindingTarget p) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- Compute the correct parameters from a field description and security goals:
    `D = ⌈(λ+1+2·q_H)/fieldBits⌉`, `k = ⌈λ/fieldBits⌉`, `S = ⌈λ/8⌉`. -/
def ofField (fieldBits lam qBits : Nat) : MerkleHasherParams where
  fieldBits   := fieldBits
  digestElems := ceilDiv (lam + 1 + 2 * qBits) fieldBits
  saltElems   := ceilDiv lam fieldBits
  saltBytes   := ceilDiv lam 8
  lam         := lam
  qBits       := qBits

theorem meetsBindingTarget_ofField (fieldBits lam qBits : Nat) (hfb : 0 < fieldBits) :
    (ofField fieldBits lam qBits).MeetsBindingTarget := by
  unfold MeetsBindingTarget kappa ofField
  simp only
  exact le_mul_ceilDiv _ _ hfb

/-- Concrete BabyBear / KoalaBear / M31 parameters (⌊log₂ |F|⌋ = 30). -/
def babyBear (lam qBits : Nat) : MerkleHasherParams := ofField 30 lam qBits

/-- Concrete Goldilocks parameters (⌊log₂ |F|⌋ = 63). -/
def goldilocks (lam qBits : Nat) : MerkleHasherParams := ofField 63 lam qBits

/-- Concrete BLS12-381 scalar-field parameters (⌊log₂ |F|⌋ = 254). -/
def bls12_381 (lam qBits : Nat) : MerkleHasherParams := ofField 254 lam qBits

theorem babyBear_meetsBindingTarget (lam qBits : Nat) :
    (babyBear lam qBits).MeetsBindingTarget :=
  meetsBindingTarget_ofField 30 lam qBits (by norm_num)

-- Worked example: BabyBear at λ=128, q_H=64 → D=9, κ=270.
example : (babyBear 128 64).digestElems = 9   := by native_decide
example : (babyBear 128 64).kappa       = 270 := by native_decide
example : (babyBear 128 64).saltElems   = 5   := by native_decide

end MerkleHasherParams

/-- **Arithmetic bridge.** The birthday bound `q(q-1)/2^(κ+1)` is at most `2^(-λ)` whenever
    the query count fits in `q ≤ 2^q_H` and the digest absorbs the slack `λ + 1 + 2·q_H ≤ κ`. -/
theorem collisionBound_le_inv_pow {κ q lam qBits : Nat}
    (hq : q ≤ 2 ^ qBits)
    (hκ : lam + 1 + 2 * qBits ≤ κ) :
    collisionBound κ q ≤ ((2 : ENNReal) ^ lam)⁻¹ := by
  unfold collisionBound
  -- 0. Useful non-zero / non-top facts.
  have h2lam0 : (2 : ENNReal) ^ lam ≠ 0 := by positivity
  have h2lamT : (2 : ENNReal) ^ lam ≠ ∞ := ENNReal.pow_ne_top (by simp)
  have h2kap0 : (2 : ENNReal) ^ (κ + 1) ≠ 0 := by positivity
  have h2kapT : (2 : ENNReal) ^ (κ + 1) ≠ ∞ := ENNReal.pow_ne_top (by simp)
  -- 1. Numerator: q(q-1) ≤ q² ≤ (2^q_H)² = 2^(2·q_H).
  have hnum : (q * (q - 1) : ENNReal) ≤ ((2 : ENNReal) ^ (2 * qBits)) := by
    rcases Nat.eq_zero_or_pos q with rfl | hq1
    · simp
    · have hq1' : 1 ≤ q := hq1
      have hqq : q * (q - 1) ≤ q ^ 2 := by nlinarith [Nat.sub_le q 1]
      have hq2 : q ^ 2 ≤ 2 ^ (2 * qBits) := by
        calc q ^ 2 ≤ (2 ^ qBits) ^ 2 := Nat.pow_le_pow_left hq 2
          _ = 2 ^ (2 * qBits) := by ring
      calc (q * (q - 1) : ENNReal)
          = ((q * (q - 1) : ℕ) : ENNReal) := by push_cast; rfl
        _ ≤ ((q ^ 2 : ℕ) : ENNReal) := by exact_mod_cast hqq
        _ ≤ ((2 ^ (2 * qBits) : ℕ) : ENNReal) := by exact_mod_cast hq2
        _ = (2 : ENNReal) ^ (2 * qBits) := by push_cast; rfl
  -- 2. Denominator slack: 2·q_H + λ + 1 ≤ κ + 1, so 2^(κ+1) ≥ 2^(2·q_H) · 2^λ.
  have hdenom : (2 : ENNReal) ^ (2 * qBits) * (2 : ENNReal) ^ lam ≤ (2 : ENNReal) ^ (κ + 1) := by
    rw [← pow_add]
    apply pow_le_pow_right₀ (by norm_num : (1 : ENNReal) ≤ 2)
    omega
  -- 3. Combine: q(q-1)/2^(κ+1) ≤ 2^(2q_H)/2^(κ+1) ≤ 1/2^λ.
  calc (q * (q - 1) : ENNReal) / 2 ^ (κ + 1)
      ≤ (2 : ENNReal) ^ (2 * qBits) / 2 ^ (κ + 1) := by
          apply ENNReal.div_le_div_right hnum
    _ ≤ ((2 : ENNReal) ^ lam)⁻¹ := by
          rw [ENNReal.div_le_iff h2kap0 h2kapT, ← ENNReal.div_eq_inv_mul,
              ENNReal.le_div_iff_mul_le (Or.inl h2lam0) (Or.inl h2lamT)]
          exact hdenom

/-- **Generic binding security.** Any field meeting `MeetsBindingTarget` gives
    `λ`-bit position binding in the ROM — one proof for all concrete fields. -/
theorem instantiation_binding_secure
    {S : Type} [MerkleShape S]
    (p : MerkleHasherParams) (htarget : p.MeetsBindingTarget)
    [Nonempty (MerkleCommitment (ROHasher.ROHasherValue (MerkleHasherParams.kappa p)) S)]
    {q : Nat} (hq : q ≤ 2 ^ p.qBits)
    (A : HasPositionBinding.BindingAdversary
           (V := MerkleCommitment (ROHasher.ROHasherValue p.kappa) S) p.kappa q) :
    HasPositionBinding.bindingAdvantage A ≤ ((2 : ENNReal) ^ p.lam)⁻¹ :=
  (HasPositionBinding.binding_bound A).trans
    (collisionBound_le_inv_pow hq htarget)

/-- **BabyBear binding security.** No hypothesis required — `MeetsBindingTarget` is discharged
    by `babyBear_meetsBindingTarget`. -/
theorem babyBear_binding_secure
    {S : Type} [MerkleShape S]
    (lam qBits : Nat)
    [Nonempty (MerkleCommitment
      (ROHasher.ROHasherValue ((MerkleHasherParams.babyBear lam qBits).kappa)) S)]
    {q : Nat} (hq : q ≤ 2 ^ qBits)
    (A : HasPositionBinding.BindingAdversary
           (V := MerkleCommitment
             (ROHasher.ROHasherValue ((MerkleHasherParams.babyBear lam qBits).kappa)) S)
           (MerkleHasherParams.babyBear lam qBits).kappa q) :
    HasPositionBinding.bindingAdvantage A ≤ ((2 : ENNReal) ^ lam)⁻¹ :=
  instantiation_binding_secure (MerkleHasherParams.babyBear lam qBits)
    (MerkleHasherParams.babyBear_meetsBindingTarget lam qBits) hq A

end VectorCommitment.Probability.Instances
