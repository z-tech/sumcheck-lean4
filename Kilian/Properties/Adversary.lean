/-
Copyright (c) 2026 LeanStuff contributors. All rights reserved.
-/
import Kilian.Src.Construction
import Kilian.Src.Honest
import PCP.Src.Security.Soundness
import VectorCommitment.Properties.Probability.RandomOracle

/-!
# Kilian argument adversary — two-phase OracleComp

An adversary `P̃` against the Kilian-compiled argument has the
two-phase shape that the soundness analysis (paper §5, Construction 5.5)
needs to exploit:

* **Commit phase** `P̃(pp, η)` → `(x, cm, aux)` : sample auxiliary input
  `η`, output the chosen statement `x`, a commitment `cm`, and a state
  `aux` carried into the next phase.

* **Response phase** `P̃(aux, ρ)` → `(Q, ans, pf)` : on verifier
  randomness `ρ`, return the third-message reply. This phase is
  **re-runnable** on the same `aux` with different `ρ`s — the reductor
  `R` (Construction 5.5) samples `N = ℓ / ε` fresh challenges and calls
  the response phase on each, harvesting a multi-sample to stitch into a
  candidate PCP string.

Both phases live in the `OracleComp` monad, so the adversary has random-
oracle access throughout. The `spec : OracleSpec` parameter lets the
adversary speak whatever oracle the chosen security model fixes; for
ROM-Merkle, this is `ROHasher.MerkleROSpec κ`.

The auxiliary types `AuxInput` / `AuxState` are part of the structure so
each adversary can carry whatever bookkeeping it needs across phases
without forcing a particular representation.

## References

* Chiesa, Dall'Agnol, Guan, Spooner, Yogev,
  *Untangling the Security of Kilian's Protocol*,
  [eprint 2024/1434](https://eprint.iacr.org/2024/1434),
  §5.1 (security reduction) and Constructions 5.4–5.5.
-/

namespace Kilian

/-- Two-phase Kilian adversary against the compiled 3-message argument.

    `spec` fixes the random-oracle spec (digest length, query domain).
    Concrete instantiations: ROM-Merkle uses `ROHasher.MerkleROSpec κ`. -/
structure Adversary (P V : Type) [PCPSystem P] [VectorCommitment V]
    [KilianCompatible P V] (spec : OracleSpec) where
  /-- Auxiliary input type. The paper's `η`; lets the adversary depend
      on outside-distribution randomness sampled before phase 1. For the
      simplest adversaries this is `Unit`. -/
  AuxInput : Type
  /-- The distribution from which `η` is drawn (paper's `η ← D`). -/
  auxDist : PMF AuxInput
  /-- Internal state passed from commit phase to response phase. -/
  AuxState : Type
  /-- Phase 1 — commitment. Given universal params and the sampled
      auxiliary input, choose a statement and produce a VC commitment.
      Carries any state the response phase will need. -/
  commitPhase : VectorCommitment.UniversalParams V → AuxInput →
                OracleComp spec
                  (PCPSystem.Statement P ×
                   VectorCommitment.Commitment V ×
                   AuxState)
  /-- Phase 2 — response. Given the carried state and the verifier's
      challenge `ρ`, produce the third message: claimed values at the
      queried positions and the VC opening proof.

      The queried positions are deterministic from `(x, ρ)` via
      `PCPSystem.verifierQueries` — both honest prover and verifier
      compute them identically (see
      [`Kilian/Src/Honest.lean`](../Src/Honest.lean)), so they are not
      part of the adversary's output. Construction 5.5's reductor `R`
      reconstructs them externally when it processes phase-2 samples.

      Re-runnable: `R` calls this many times with different `ρ` on the
      same `AuxState`. -/
  responsePhase : AuxState → PCPSystem.Randomness P →
                  OracleComp spec
                    (List (PCPSystem.Alphabet P) ×
                     VectorCommitment.Proof V)

namespace Adversary

variable {P V : Type} [PCPSystem P] [VectorCommitment V] [KilianCompatible P V]
  {spec : OracleSpec}

/-- One full run of the adversary against the verifier.

    Samples `η`, runs phase 1 to get `(x, cm, aux)`, samples `ρ` from the
    PCP's randomness distribution, runs phase 2 to get the reply, then
    returns the assembled `(statement, transcript)` pair so a separate
    `verifyTranscript` call can decide acceptance.

    The result is an `OracleComp` over the RO; closing the monad with
    `simulateQ` (after also closing over `auxDist` and the PCP randomness
    distribution) gives the full `PMF` over outcomes. -/
noncomputable def runOnce (A : Adversary P V spec)
    (pp : VectorCommitment.UniversalParams V)
    (η : A.AuxInput) (ρ : PCPSystem.Randomness P) :
    OracleComp spec
      (PCPSystem.Statement P × Transcript P V) := do
  let phase1 ← A.commitPhase pp η
  let x   := phase1.1
  let cm  := phase1.2.1
  let aux := phase1.2.2
  let reply ← A.responsePhase aux ρ
  let values := reply.1
  let proof  := reply.2
  pure (x,
        { commitment := cm,
          randomness := ρ,
          values     := values,
          proof      := proof })

end Adversary

end Kilian

-- The Kilian argument's soundness error `argumentError` is defined in
-- [`Lemma53.lean`] using the same joint experiment that hosts the bad
-- event and the case events. That sharing lets `argumentError_split`
-- in [`Theorem51.lean`] proceed as a single outer-measure manipulation
-- without an intervening marginalization identity between PMFs.

