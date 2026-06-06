/-
Copyright (c) 2026 LeanStuff contributors. All rights reserved.
-/
import VectorCommitment.Src.Security.PositionBinding
import VectorCommitment.Src.Merkle.Instance
import VectorCommitment.Properties.Probability.ROHasher
import VectorCommitment.Properties.Probability.Collision
import VectorCommitment.Properties.Probability.CheckOracle
import VectorCommitment.Properties.Probability.Coupling
import VectorCommitment.Properties.Probability.TraceCollision
import VectorCommitment.Properties.Theorems.Binding

/-!
# ROM instance: position binding for RO-derived Merkle commitments

Discharges `HasPositionBinding (MerkleCommitment (ROHasherValue κ) S)`
for every digest length `κ` and Merkle shape `S`, in the random-oracle model.

## The experiment (shared oracle)

`bindingAdvantage` runs the adversary and validates its claimed break by
re-verifying *both* openings with `ROHasher.checkOracle` (`Verify^H`) against
the **same** lazily-sampled oracle the adversary queried. The advantage is the
probability the experiment returns `true` (distinct values, both openings
verify) — pinned to a real game, never a free quantity.

## Reduction (two steps)

```
Pr[A wins]
  ≤ Pr[trace has a collision]      [binding_win_le_trace_collision — structural]
  ≤ collisionBound κ q             [coupling_trace_le_collisionBound — proved]
```

**Step 2** is `coupling_trace_le_collisionBound` (`Coupling.lean`,
machine-checked). **Step 1** is the structural fact that a winning break with a
*collision-free* trace is impossible: under an injective realized hash the two
accepting paths to the same root force `value₀ = value₁` (the deterministic
spine `mt_binding`, `Theorems/Binding.lean`, is fully proved). Lifting
`mt_binding` from "globally injective hasher" to "injective on the query log"
across the `OracleComp` monad is isolated as `binding_win_le_trace_collision`.
-/

namespace VectorCommitment.Probability.Instances

open VectorCommitment.Security VectorCommitment.Probability
open scoped Classical

variable (κ : Nat) (S : Type) [MerkleShape S]
  [Nonempty (MerkleCommitment (ROHasher.ROHasherValue κ) S)]

/-- The inner experiment: run the adversary, then re-verify both openings with
    `checkOracle` against the shared oracle; win on distinct values with both
    accepting. `n` is the leaf count of the scheme's (public) tree shape. -/
private noncomputable def bindingInner
    (A : OracleComp (ROHasher.MerkleROSpec κ)
           (BindingBreak (MerkleCommitment (ROHasher.ROHasherValue κ) S))) :
    OracleComp (ROHasher.MerkleROSpec κ) Bool :=
  let n := MerkleShape.numLeaves
    (Classical.ofNonempty : MerkleCommitment (ROHasher.ROHasherValue κ) S).shape
  do
    let b ← A
    let r₀ ← ROHasher.checkOracle n b.commitment.root
              { indices := [b.index], values := [b.value₀] } b.proof₀
    let r₁ ← ROHasher.checkOracle n b.commitment.root
              { indices := [b.index], values := [b.value₁] } b.proof₁
    pure (decide (b.value₀ ≠ b.value₁) && r₀ && r₁)

/-- **Step 1 (structural).** A winning outcome has a colliding trace.

    If both `checkOracle` calls accept with `value₀ ≠ value₁`, the two
    authentication paths reconstruct the same root from distinct leaves; were
    the trace collision-free, `accepted_value_unique` would force
    `value₀ = value₁` — contradiction. -/
private lemma binding_win_le_trace_collision
    (A : OracleComp (ROHasher.MerkleROSpec κ)
           (BindingBreak (MerkleCommitment (ROHasher.ROHasherValue κ) S))) :
    ((bindingInner κ S A).run QueryLog.empty).toOuterMeasure {p | p.1 = true}
      ≤ ((bindingInner κ S A).run QueryLog.empty).toOuterMeasure
          {p | QueryLog.hasCollision p.2} := by
  apply toOuterMeasure_mono_support
  rintro ⟨bout, logf⟩ hsupp hwin
  simp only [Set.mem_setOf_eq] at hwin ⊢
  by_contra hnc
  rw [bindingInner, run_bind'] at hsupp
  simp only [PMF.support_bind, Set.mem_iUnion] at hsupp
  obtain ⟨⟨b, logA⟩, hA, hsupp⟩ := hsupp
  rw [run_bind'] at hsupp
  simp only [PMF.support_bind, Set.mem_iUnion] at hsupp
  obtain ⟨⟨r0, log1⟩, hc0, hsupp⟩ := hsupp
  rw [run_bind'] at hsupp
  simp only [PMF.support_bind, Set.mem_iUnion] at hsupp
  obtain ⟨⟨r1, log2⟩, hc1, hsupp⟩ := hsupp
  rw [run_pure, PMF.support_pure, Set.mem_singleton_iff] at hsupp
  obtain ⟨hbeq, hlogeq⟩ := Prod.ext_iff.mp hsupp
  subst hlogeq
  rw [hwin, eq_comm, Bool.and_eq_true, Bool.and_eq_true] at hbeq
  obtain ⟨⟨hne, hr0⟩, hr1⟩ := hbeq
  subst hr0; subst hr1
  obtain ⟨s0, cp0, _, hlen0, hrec0⟩ := checkOracle_singleton_accept hc0
  obtain ⟨s1, cp1, _, hlen1, hrec1⟩ := checkOracle_singleton_accept hc1
  have hndA : (logA.map Prod.fst).Nodup :=
    run_nodup _ QueryLog.empty (b, logA) hA (by simp [QueryLog.empty])
  have hne' : b.value₀ ≠ b.value₁ := by simpa using hne
  exact absurd (accepted_value_unique hndA (hlen0.trans hlen1.symm) hnc hrec0 hrec1) hne'

/-- Position binding for the RO-derived Merkle commitment.

    The adversary at budget `q` is a `q`-query-bounded oracle computation: the
    subtype carries the proof that the *whole* experiment (adversary plus the
    bounded `checkOracle` verification) stays within `q` distinct oracle
    queries, so the birthday bound applies. No budget `sorry` is incurred. -/
noncomputable instance :
    HasPositionBinding (MerkleCommitment (ROHasher.ROHasherValue κ) S) where
  BindingAdversary := fun _ q =>
    { A : OracleComp (ROHasher.MerkleROSpec κ)
            (BindingBreak (MerkleCommitment (ROHasher.ROHasherValue κ) S)) //
      OracleComp.QueryBudget (bindingInner κ S A) q }
  -- Shared-oracle game: validate the break with `checkOracle` against the
  -- same oracle the adversary queried (the advantage is a real win-probability).
  bindingAdvantage := fun {_ _} A => OracleComp.simulateQ (bindingInner κ S A.1) true
  bindingError := fun _ q => Probability.collisionBound κ q
  -- win ≤ trace-collision ≤ collisionBound.
  binding_bound := by
    intro _ q A
    show OracleComp.simulateQ (bindingInner κ S A.1) true ≤ Probability.collisionBound κ q
    simp only [OracleComp.simulateQ]
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    have Hpre : (Prod.fst ⁻¹' ({true} : Set Bool)) =
        {p : Bool × QueryLog (ROHasher.MerkleROSpec κ) | p.1 = true} := by
      ext ⟨b, _⟩; simp
    rw [Hpre]
    exact (binding_win_le_trace_collision κ S A.1).trans
            (coupling_trace_le_collisionBound (bindingInner κ S A.1) q A.2)

end VectorCommitment.Probability.Instances
