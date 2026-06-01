/-
Copyright (c) 2026 LeanStuff contributors. All rights reserved.
-/
import Mathlib.Data.ENNReal.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# `PCPSystem` — abstract typeclass for probabilistically checkable proofs

This typeclass abstracts the interface to a PCP for a relation `R`.
Mirrors the shape of `VectorCommitment` in
[`VectorCommitment/Src/Trait.lean`](../../VectorCommitment/Src/Trait.lean):
typed associated members, model-neutral, no probabilistic content in
the class itself.

Higher-level constructions (Kilian's protocol, the BCS transform) bind
on `[PCPSystem P]` to access the PCP's statement / alphabet / proof
length / query complexity / soundness error abstractly.

## References

* S. Arora, S. Safra, *Probabilistic checking of proofs*, JACM 1998.
* A. Chiesa, E. Yogev, *Building Cryptographic Proofs from Hash
  Functions*, §17 (PCP definitions).
* A. Chiesa, M. Dall'Agnol, Z. Guan, N. Spooner, E. Yogev,
  *Untangling the Security of Kilian's Protocol*,
  [eprint 2024/1434](https://eprint.iacr.org/2024/1434), §2–3.
-/

/-- A probabilistically-checkable proof system. Carries the types of
    statements / witnesses / proof alphabet / verifier randomness, plus
    the honest prover, the verifier's query and decision functions, and
    the soundness error.

    `P` is the "scheme handle" — a type-level token that allows
    multiple PCP systems for the same relation to coexist.

    The PCP is for a fixed relation `relation : Statement → Witness → Prop`
    (paper Definition 3.13). The induced language is
    `language x ↔ ∃ w, relation x w`; this predicate is the precondition
    of the soundness theorem ("for `x ∉ L(R)`, no `pi` makes V accept
    with prob > ε_PCP"). See [`HasSoundness`](Security/Soundness.lean). -/
class PCPSystem (P : Type) where
  /-- Statement type (input to the PCP — e.g. SAT formulas, R1CS instances). -/
  Statement : Type
  /-- Witness type for the honest prover. -/
  Witness : Type
  /-- The relation the PCP is for. Soundness is stated for `x ∉ L(relation)`. -/
  relation : Statement → Witness → Prop
  /-- The PCP proof-string alphabet. Typically `Bool`, a field, or
      a small finite type. -/
  Alphabet : Type
  /-- The verifier's randomness space. -/
  Randomness : Type
  /-- The distribution on `Randomness` from which the verifier samples
      its random tape. For classical PCPs over `{0,1}^r` this is the
      uniform distribution; the field lets a concrete instance choose. -/
  randomnessDist : PMF Randomness
  /-- Length of the PCP proof string as a function of statement size `n`. -/
  proofLength : ℕ → ℕ
  /-- Number of queries the verifier makes, as a function of `n`. -/
  queryComplexity : ℕ → ℕ
  /-- The honest prover: given statement and witness, output the PCP
      string. Length should equal `proofLength n` for an honestly-formed
      input; this is not enforced at the typeclass level. -/
  honestProver : Statement → Witness → List Alphabet
  /-- The verifier's query function: given the statement and its random
      tape, list the indices of the PCP it will probe. Length should
      equal `queryComplexity n`. -/
  verifierQueries : Statement → Randomness → List ℕ
  /-- The verifier's decision function: given the statement, its
      randomness, and the queried responses, accept or reject. -/
  verifierDecide : Statement → Randomness → List Alphabet → Bool

namespace PCPSystem

variable {P : Type} [PCPSystem P]

/-- The language induced by a PCP's relation: statements that have
    *some* witness. Soundness is stated relative to this language. -/
def language (P : Type) [PCPSystem P] (x : Statement P) : Prop :=
  ∃ w, PCPSystem.relation (P := P) x w

/-- Read a candidate PCP string at the verifier's queried positions.
    Out-of-range queries take the supplied `default`. -/
def readAt (pi : List (Alphabet P)) (queries : List ℕ)
    (default : Alphabet P) : List (Alphabet P) :=
  queries.map (fun i => (pi[i]?).getD default)

/-- The PCP verifier's acceptance probability on candidate string `pi`
    and statement `x`, taken over the verifier's randomness.

    This is the quantity bounded by `soundnessError` for `x ∉ L`
    (see [`HasSoundness`](Security/Soundness.lean)). -/
noncomputable def acceptanceProb [Inhabited (Alphabet P)]
    (x : Statement P) (pi : List (Alphabet P)) : ENNReal :=
  (PCPSystem.randomnessDist (P := P)).toOuterMeasure
    {ρ : Randomness P |
      PCPSystem.verifierDecide (P := P) x ρ
        (readAt (P := P) pi (PCPSystem.verifierQueries (P := P) x ρ) default) = true}

end PCPSystem
