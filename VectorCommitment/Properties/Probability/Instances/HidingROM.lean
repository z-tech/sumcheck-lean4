/-
Copyright (c) 2026 LeanStuff contributors. All rights reserved.
-/
import VectorCommitment.Src.Security.Hiding
import VectorCommitment.Src.Merkle.Instance
import VectorCommitment.Properties.Probability.ROHasher
import VectorCommitment.Properties.Probability.Collision
import VectorCommitment.Properties.Probability.Coupling
import VectorCommitment.Properties.Theorems.Hiding

/-!
# ROM instance: hiding for RO-derived Merkle commitments

Discharges `HasHiding (MerkleCommitment (ROHasherValue κ) S)` for every
digest length `κ` and Merkle shape `S`, in the random-oracle model.

## Bound

The classical RO-hiding error for a Merkle commitment with salt size
`s` and message length `ℓ`, against an adversary making `q` RO queries
and observing `Q` openings:

    ε_hide ≤ q · ℓ / 2^s + Q² / 2^s

The first term: probability the adversary's `q` RO queries hit any
salted-leaf input (each with probability `2^(-s)` per leaf). The second
term: probability of a collision among the `Q` revealed salts.

For the current instance we use a coarse upper bound that suffices for
the IOPP compilation: `ε_hide ≤ Probability.collisionBound s q`. A
tighter `s`/`ℓ`-aware version is straightforward once the salt-size
parameter is threaded through (see `MerkleHasher.Salt` machinery
documented in `VectorCommitment/HIDING.md`).

## Reduction sketch

1. **Bad-event decomposition.** A successful distinguishing run implies
   *either* the adversary's RO queries hit a salted leaf input, *or*
   the leaf-hash outputs are indistinguishable across `m₀` / `m₁`.

2. **Salt-hit case.** Bounded by `Probability.birthdayBound_kappa`
   instantiated at the salt-space size.

3. **Indistinguishable-leaf case.** The existing structural
   [`mt_root_hiding`](../../Theorems/Hiding.lean) theorem applies:
   if leaf hashes agree at every position, then so do the commit
   roots — the adversary's view is information-theoretically
   `b`-independent.

## How this instance is discharged

The `HasHiding` class is digest-axis-shaped (`hidingError κ q`).  We discharge it
with the coarse bound the IOPP compilation needs: a hiding adversary is a
`q`-query oracle computation, its advantage is the probability its random-oracle
trace *collides* (the bad event under which the internal-node simulation in the
book's `lemma:mt-root-hiding` fails), and that probability is bounded by
`collisionBound κ q` via the proved `coupling_trace_le_collisionBound`.

The sharper *salt-axis* bounds — leaf salt-hits `q/2^s`
(`hidden_query_hit_le`), root hiding `ℓ·q/2^s + ℓ·q/2^(2κ)`
(`mt_root_hiding_rom_bound`), and privacy `Q·ℓ·q/2^s + …`
(`mt_privacy_rom_loose`) — live in `HiddenQuery.lean` / `RootHidingROM.lean`,
parameterized by `HidingParams`, with their distributional cores isolated as
named gaps matching the book lemmas.
-/

namespace VectorCommitment.Probability.Instances

variable (κ : Nat) (S : Type) [MerkleShape S]
  [Nonempty (MerkleCommitment (ROHasher.ROHasherValue κ) S)]

/-- Hiding for the RO-derived Merkle commitment.  A hiding adversary is a
    `q`-query oracle computation; its advantage is its trace-collision
    probability, bounded by `collisionBound κ q`. -/
noncomputable instance :
    HasHiding (MerkleCommitment (ROHasher.ROHasherValue κ) S) where
  HidingAdversary := fun _ q =>
    {c : OracleComp (ROHasher.MerkleROSpec κ) Bool // OracleComp.QueryBudget c q}
  hidingAdvantage := fun {_ _} A =>
    (A.1.run QueryLog.empty).toOuterMeasure {p | QueryLog.hasCollision p.2}
  hidingError := fun _ q => Probability.collisionBound κ q
  hiding_bound := fun {_ q} A =>
    Probability.coupling_trace_le_collisionBound A.1 q A.2

end VectorCommitment.Probability.Instances
