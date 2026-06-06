/-
Copyright (c) 2026 LeanStuff contributors. All rights reserved.
-/
import VectorCommitment.Src.Security.Extractability
import VectorCommitment.Src.Merkle.Instance
import VectorCommitment.Properties.Probability.ROHasher
import VectorCommitment.Properties.Probability.Collision
import VectorCommitment.Properties.Probability.CheckOracle
import VectorCommitment.Properties.Probability.Coupling
import VectorCommitment.Properties.Theorems.Extractability

/-!
# ROM instance: straightline extractability for RO-derived Merkle commitments

Discharges `HasStraightlineExtractor (MerkleCommitment (ROHasherValue κ) S)` in
the random-oracle model. The straightline extractor `ROHasher.cacheExtract`
reads the finished query log and walks the digest tree from the committed root
down to the requested leaf.

## The experiment

`extractionFailureAdvantage` runs the adversary, re-verifies its opening with
`ROHasher.checkOracle` (`Verify^H`) against the shared oracle, and — reading the
*finished* log — flags a **failure** when the opening verifies yet some opened
index's claimed leaf disagrees with the one `cacheExtract` recovers. (Because
the extractor reads the final trace, no in-computation log access is needed.)

## Reduction (two steps)

```
Pr[extraction fails]
  ≤ Pr[trace has a collision]      [extraction_win_le_trace_collision — structural]
  ≤ collisionBound κ q             [coupling_trace_le_collisionBound — proved]
```

**Step 2** is machine-checked (`Coupling.lean`). **Step 1** is the structural
fact that a verified-but-mis-extracted opening forces two distinct accepting
authentication paths to the same root — impossible under a collision-free
trace by `mt_multi_extractability` (`Theorems/Extractability.lean`, proved). The
monad-level transport is isolated as `extraction_win_le_trace_collision`.
-/

namespace VectorCommitment.Probability.Instances

open VectorCommitment.Probability
open scoped Classical

variable (κ : Nat) (S : Type) [MerkleShape S]
  [Nonempty (MerkleCommitment (ROHasher.ROHasherValue κ) S)]

/-- The adversary's output: a commitment, a multi-index opening request, and a
    proof. -/
private abbrev ExtractBreak :=
  Committed (ROHasher.ROHasherValue κ) S × List Nat ×
    List (List.Vector Bool κ) × OpeningProof (ROHasher.ROHasherValue κ)

/-- Leaf count of the scheme's (public) tree shape. -/
private noncomputable def nLeaves : Nat :=
  MerkleShape.numLeaves
    (Classical.ofNonempty : MerkleCommitment (ROHasher.ROHasherValue κ) S).shape

/-- The straightline-extraction failure flag, a pure function of the adversary's
    output and the finished trace: some opened index whose claimed leaf input
    disagrees with what `cacheExtract` recovers under the committed root. -/
private noncomputable def extractMismatch (br : ExtractBreak κ S)
    (log : QueryLog (ROHasher.MerkleROSpec κ)) : Bool :=
  ((br.2.1.zip br.2.2.1).zip br.2.2.2.entries).any (fun triple =>
    let ((i, value), (salt, _)) := triple
    !(ROHasher.cacheExtract log br.1.root (nLeaves κ S) i
        == some (ROHasher.encodeLeaf value salt)))

/-- The inner experiment: run the adversary, re-verify with `checkOracle`, and
    return the break together with the verifier's verdict. The extraction
    failure is read off the finished run by `extractMismatch`. -/
private noncomputable def extractInner
    (A : OracleComp (ROHasher.MerkleROSpec κ) (ExtractBreak κ S)) :
    OracleComp (ROHasher.MerkleROSpec κ) (ExtractBreak κ S × Bool) :=
  do
    let br ← A
    let r ← ROHasher.checkOracle (nLeaves κ S) br.1.root
              { indices := br.2.1, values := br.2.2.1 } br.2.2.2
    pure (br, r)

/-- **Step 1 (structural).** A failure outcome has a colliding trace.

    A verified opening (`checkOracle` accepts) whose claimed leaf differs from
    the cache-extracted one yields two accepting authentication paths to the
    same root; under a collision-free trace `accepted_value_unique`
    (`TraceCollision.lean`, proved) forces them equal — contradiction.

    **Status: reduced to ONE isolated bridge lemma, `cacheExtract_sound`**
    (not yet formalized): under a collision-free, functional log, an accepting
    `checkOracle` opening at `i` implies
    `cacheExtract log root n i = some (encodeLeaf value salt)` (the top-down
    extractor recovers the proof's leaf). Its three pieces are the
    `decodeDigest`/`decodeNodeInput` round-trips (inverse of `vecBytes`),
    `find?`-by-output uniqueness (collision-free ⇒ outputs injective), and the
    `descentChoices`(root→leaf) ↔ `walkCopath`(leaf→root) parity alignment.
    Given `cacheExtract_sound`, this lemma closes via `accepted_value_unique`
    exactly as `binding_win_le_trace_collision` does. -/
private lemma extraction_win_le_trace_collision
    (A : OracleComp (ROHasher.MerkleROSpec κ) (ExtractBreak κ S)) :
    ((extractInner κ S A).run QueryLog.empty).toOuterMeasure
        {p | p.1.2 = true ∧ extractMismatch κ S p.1.1 p.2 = true}
      ≤ ((extractInner κ S A).run QueryLog.empty).toOuterMeasure
          {p | QueryLog.hasCollision p.2} := by
  sorry

/-- Straightline extractability for the RO-derived Merkle commitment.

    As with binding, the adversary at budget `q` is a `q`-query-bounded oracle
    computation (subtype carrying the budget proof for the whole experiment), so
    no budget `sorry` is incurred. -/
noncomputable instance :
    HasStraightlineExtractor (MerkleCommitment (ROHasher.ROHasherValue κ) S) where
  ExtractionAdversary := fun _ q =>
    { A : OracleComp (ROHasher.MerkleROSpec κ) (ExtractBreak κ S) //
      OracleComp.QueryBudget (extractInner κ S A) q }
  -- Shared-oracle game: verdict by `checkOracle`, failure by post-hoc
  -- `cacheExtract` on the finished trace (a real win-probability).
  extractionFailureAdvantage := fun {_ _} A =>
    ((extractInner κ S A.1).run QueryLog.empty).toOuterMeasure
      {p | p.1.2 = true ∧ extractMismatch κ S p.1.1 p.2 = true}
  extractionError := fun _ q => Probability.collisionBound κ q
  -- failure ≤ trace-collision ≤ collisionBound.
  extraction_bound := by
    intro _ q A
    exact (extraction_win_le_trace_collision κ S A.1).trans
            (coupling_trace_le_collisionBound (extractInner κ S A.1) q A.2)

end VectorCommitment.Probability.Instances
