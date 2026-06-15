/-
Copyright (c) 2026 LeanStuff contributors. All rights reserved.
-/
import Kilian.Properties.Adversary

/-!
# The reductor `R` (Construction 5.5 of eprint 2024/1434)

Given a Kilian-argument adversary `A` and a (commitment, aux-state)
pair from its commit phase, the reductor `R` rewinds `A.responsePhase`
on `N = ℓ/ε` fresh verifier challenges, collects the VC-validated
replies, and post-processes them into a candidate PCP string `Π̃`
together with the "covered" position set `Q̃`.

`R` is the engine of Lemma 5.3 — the technical core of Theorem 5.1.
Its two-stage shape (sample, then post-process) mirrors the paper
exactly (Constructions 5.4 + 5.5).

## Design notes

* **RO randomness vs. PCP randomness.** `A.responsePhase` is an
  `OracleComp` (RO-randomness inside). The verifier challenges
  `ρ'_1, …, ρ'_N` are sampled at the *outer* PMF layer, before the
  reductor runs. So `sample` takes a pre-sampled list of challenges and
  threads them through `responsePhase` one by one, accumulating
  successful tuples in `OracleComp`.

* **Queries are deterministic from `(x, ρ')`.** In our protocol the
  verifier (and hence the reductor) re-derives the query set from
  `PCPSystem.verifierQueries x ρ'` — see
  [`Kilian/Src/Honest.lean`](../Src/Honest.lean) — so the sampler does
  not need the adversary to report `Q'`.

* **Post-processing is total / deterministic.** `postprocess` just
  walks the sampler's output, setting `Π̃[q] := ans[i]` at every
  position `q := Q'[i]` and union-ing into `Q̃`. No probability, no RO.

## References

* Chiesa, Dall'Agnol, Guan, Spooner, Yogev,
  *Untangling the Security of Kilian's Protocol*,
  [eprint 2024/1434](https://eprint.iacr.org/2024/1434),
  Constructions 5.4 (sampler) and 5.5 (reductor).
-/

namespace Kilian

namespace Reductor

variable {P V : Type} [PCPSystem P] [Inhabited (PCPSystem.Alphabet P)]
  [VectorCommitment V] [KilianCompatible P V]
  {spec : OracleSpec}

/-- One sampled reply from the adversary's response phase, after VC
    validation: the verifier randomness used, the claimed values, and
    the opening proof. (We retain the proof so downstream analysis can
    extract a position-binding break in Case 1 of Lemma 5.3.) -/
abbrev SampleEntry (P V : Type) [PCPSystem P] [VectorCommitment V] : Type :=
  PCPSystem.Randomness P ×
  List (PCPSystem.Alphabet P) ×
  VectorCommitment.Proof V

/-- The reductor's intermediate output: a candidate PCP string `Π̃` and
    the set `Q̃` of positions covered by at least one validated sample.

    `covered` is a `List ℕ` rather than a `Set ℕ` for computability and
    because the analysis needs an enumeration of touched positions. The
    underlying set is `covered.toFinset`. -/
structure Output (P : Type) [PCPSystem P] where
  /-- Candidate PCP string `Π̃`, length `ℓ`. -/
  pi : List (PCPSystem.Alphabet P)
  /-- Positions `Q̃ ⊆ [ℓ]` filled in by at least one validated sample. -/
  covered : List ℕ

/-- **Sampler `S` (Construction 5.4).**

    Runs `A.responsePhase` on each of the supplied challenges `rhos`,
    re-derives the query set from `(x, ρ')`, runs `VC.Check`, and
    accumulates tuples whose VC check passed.

    Returns the list of validated `(ρ', values, proof)` tuples, in
    sampled order. -/
noncomputable def sample
    (A : Adversary P V spec)
    (vk : VectorCommitment.VerifierKey V)
    (x : PCPSystem.Statement P)
    (cm : VectorCommitment.Commitment V)
    (aux : A.AuxState)
    (rhos : List (PCPSystem.Randomness P)) :
    OracleComp spec (List (SampleEntry P V)) :=
  rhos.foldlM (init := ([] : List (SampleEntry P V))) fun acc ρ' => do
    let reply ← A.responsePhase aux ρ'
    let values := reply.1
    let proof  := reply.2
    let queries   : List ℕ := PCPSystem.verifierQueries (P := P) x ρ'
    let queries_V := KilianCompatible.castIndex (P := P) (V := V) queries
    let values_V  := KilianCompatible.castAlphabet (P := P) (V := V) values
    let vc_ok     :=
      VectorCommitment.check (V := V) vk cm queries_V values_V proof
    if vc_ok then
      pure (acc ++ [(ρ', values, proof)])
    else
      pure acc

/-- Stitch a single validated sample into the running output. For every
    `(q, v) ∈ zip Q' ans`, set `Π̃[q] := v` and add `q` to the covered
    set. Out-of-range `q` are silently ignored by `List.set`. -/
def stitchOne (x : PCPSystem.Statement P) (out : Output P)
    (entry : SampleEntry P V) : Output P :=
  let ρ'      : PCPSystem.Randomness P := entry.1
  let values  : List (PCPSystem.Alphabet P) := entry.2.1
  let queries : List ℕ := PCPSystem.verifierQueries (P := P) x ρ'
  let pi' :=
    (queries.zip values).foldl (init := out.pi) fun acc qv =>
      acc.set qv.1 qv.2
  { pi := pi', covered := out.covered ++ queries }

/-- **Post-processor `R_post` (Construction 5.5).**

    Initializes `Π̃ := default^ℓ` and `Q̃ := ∅`; folds the sampler's
    output through `stitchOne`. Deterministic, no oracle. -/
def postprocess (x : PCPSystem.Statement P)
    (samples : List (SampleEntry P V)) (ℓ : ℕ) : Output P :=
  samples.foldl (init := { pi := List.replicate ℓ default, covered := [] })
    (stitchOne (V := V) x)

/-- **The reductor `R` (Construction 5.5, full).**

    Calls `sample` on the supplied challenges, then `postprocess` to
    stitch the validated samples into a candidate PCP string of length
    `proofLength n`.

    The number of samples `N` and the slack `ε` are *implicit* in the
    length of `rhos`: the caller is expected to pass `N := ⌈ℓ / ε⌉`
    fresh challenges, matching the paper's analysis. We keep `rhos` an
    explicit argument so this file imposes no commitment to a specific
    sampling distribution; the soundness experiment in
    [`Adversary.argumentError`](Adversary.lean) closes that choice. -/
noncomputable def reduce
    (A : Adversary P V spec)
    (vk : VectorCommitment.VerifierKey V)
    (x : PCPSystem.Statement P)
    (cm : VectorCommitment.Commitment V)
    (aux : A.AuxState)
    (rhos : List (PCPSystem.Randomness P))
    (ℓ : ℕ) :
    OracleComp spec (Output P) := do
  let samples ← sample A vk x cm aux rhos
  pure (postprocess (V := V) x samples ℓ)

end Reductor

end Kilian
