/- VectorCommitment/Interface.lean
   ENTRY POINT for the Vector Commitment verification path.
   Layers: L1 operational trait · L2 Merkle realization
           L3 security classes  · L4 ROM discharge · L5 hasher instantiation
-/
import VectorCommitment.Src
import VectorCommitment.Properties

namespace VectorCommitment.Interface
open VectorCommitment VectorCommitment.Security VectorCommitment.Probability
open VectorCommitment.Probability.Instances

/-! ## L1/L2: the scheme you verify against -/
/-- The canonical Merkle VC over a κ-bit ROM hasher and a tree shape `S`. -/
abbrev MerkleVC (κ : Nat) (S : Type) [MerkleShape S] :=
  MerkleCommitment (ROHasher.ROHasherValue κ) S

/-! ## L3: the four security notions -/
-- HasPositionBinding, HasStraightlineExtractor, HasHiding, HasEquivocation
-- (instances discharged at L4 for MerkleVC)

/-! ## L4: machine-checked cores -/
/-- The finite iid birthday bound: n samples from range R collide with prob ≤ n(n-1)/(2|R|). -/
alias birthdayCollisionBound := Probability.birthdayBound

/-- The lazy-oracle trace collision bound: any q-query computation has a colliding trace
    with probability at most collisionBound κ q = q(q-1)/2^(κ+1). -/
alias romTraceCollisionBound := Probability.coupling_trace_le_collisionBound

/-- The concrete collision error expression: q(q-1)/2^(κ+1). -/
noncomputable abbrev collisionProbability := @Probability.collisionBound

/-! ## L5: hasher instantiation -/
-- MerkleHasherParams: the parameter record (fieldBits, D, k, S, λ, q_H)
-- ofField: computes D = ⌈(λ+1+2q_H)/fieldBits⌉, k, S from field+security goals
-- babyBear, goldilocks, bls12_381: concrete per-field constructors
-- instantiation_binding_secure: generic λ-bit binding for MeetsBindingTarget params
-- babyBear_binding_secure: zero-hypothesis BabyBear/KoalaBear/M31 capstone

/-! ## Status
    binding        ✅ proven, axiom-clean [propext, Classical.choice, Quot.sound]
    extractability ◐ reduced to cacheExtract_sound (1 sorry in ExtractabilityROM)
    hiding         ✗ parameters computed (k, S); ROM proof pending H1–H5
    equivocation   ✗ out of scope (programmable RO)                             -/

end VectorCommitment.Interface
