/-
Copyright (c) 2026 LeanStuff contributors. All rights reserved.
-/
import VectorCommitment.Src.Trait
import Mathlib.Data.ENNReal.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Position binding — abstract security obligation

This file declares the model-agnostic typeclass `HasPositionBinding`.
The property: no adversary, in any computational model the instance
specifies, can produce two distinct accepting openings of the same
position of a single commitment.

A security model discharges this class by:
  * supplying an `Adversary` type capturing its computational shape
    (ROM: an `OracleComp` returning a candidate break;
     standard model: a runtime-bounded reduction to an assumption),
  * defining the adversary's binding advantage,
  * exhibiting an `Error` bound and proving the advantage is below it.

Model-specific instances live under:
  * `VectorCommitment/Properties/Probability/Instances/BindingROM.lean`
  * `VectorCommitment/Properties/StandardModel/Instances/BindingCR.lean`  (reserved)

Higher-level protocol theorems (Kilian's Theorem 5.1, BCS soundness,
IOPP compilations) consume this class abstractly and stay
model-neutral.
-/

namespace VectorCommitment.Security

open VectorCommitment

/-- A position-binding break: a commitment together with two singleton
    openings of the same position that disagree on the revealed value.

    Each opening is `(value, proof)`; the values differ; the verifier
    accepts both. Validity against a specific `vk` is captured by
    `BindingBreak.IsValid` below.

    A break does not by itself carry the verifier key — the binding game
    samples the key and then asks the adversary to produce a break that
    is valid against it. -/
structure BindingBreak (V : Type) [VectorCommitment V] where
  commitment : Commitment V
  index      : Index V
  value₀     : Alphabet V
  value₁     : Alphabet V
  proof₀     : Proof V
  proof₁     : Proof V

/-- A break is *valid* against verifier key `vk` when both singleton
    openings pass `check` and reveal distinct values. -/
def BindingBreak.IsValid {V : Type} [VectorCommitment V]
    (vk : VerifierKey V) (b : BindingBreak V) : Prop :=
  b.value₀ ≠ b.value₁ ∧
  check vk b.commitment [b.index] [b.value₀] b.proof₀ = true ∧
  check vk b.commitment [b.index] [b.value₁] b.proof₁ = true

end VectorCommitment.Security

/-- Position-binding obligation, layered on top of the operational
    `VectorCommitment` interface.

    Game parameters:
      * `κ` — security parameter (digest length in the ROM, group
              order / hash output length in the standard model).
      * `q` — adversary resource budget (RO queries in the ROM,
              runtime bound in the standard model).

    An `instance` for a concrete commitment type `V` under a chosen
    security model discharges the four fields below. -/
class HasPositionBinding (V : Type) [VectorCommitment V] where
  /-- The adversary type at security parameter `κ` and resource
      budget `q`.

      Each model picks this concretely:
        * ROM: `OracleComp spec (BindingBreak V)` for the RO spec.
        * Standard model: a runtime-bounded reduction returning a
          `BindingBreak V` together with a witness to the assumption
          break it forces. -/
  BindingAdversary : (κ q : ℕ) → Type
  /-- The probability that running `A` yields a *valid* break, taken
      over `A`'s own coins together with any randomness the model
      supplies (lazy oracle samples in the ROM, assumption-game coins
      in the standard model). -/
  bindingAdvantage : ∀ {κ q}, BindingAdversary κ q → ENNReal
  /-- The model-specific upper bound on `bindingAdvantage`.

      Examples:
        * ROM Merkle:        `q * (q - 1) / 2 ^ (κ + 1)`  (birthday).
        * Standard-model CR: `Adv_H^CR(B)` for some reduction `B`. -/
  bindingError : (κ q : ℕ) → ENNReal
  /-- The central guarantee: every adversary's advantage is at most
      the model-specific error term. -/
  binding_bound :
    ∀ {κ q} (A : BindingAdversary κ q),
      bindingAdvantage A ≤ bindingError κ q
  /-- **Lifted binding bound — disagreement at a "covered" index of
      a multi-position opening.**

      ## Why this shape

      Higher-level theorems (notably Kilian's Theorem 5.1 / Lemma 5.3
      Case 1 — `bound_case1` in `Kilian/Properties/Lemma53.lean`) need
      to bound the probability of a "binding break" inside a *joint*
      experiment with many other moving pieces (auxiliary input
      distributions, multi-round sampling, an adversary that produces
      both openings indirectly). The classical `binding_bound` field
      bounds the advantage of an *explicit* `BindingAdversary κ q`
      against the binding game. Translating from a joint-experiment
      event back to an explicit `BindingAdversary` is mechanical but
      tedious: you must (i) construct the adversary's algorithm,
      (ii) thread the experiment's randomness through it, (iii)
      relate its advantage to the original event's probability.

      `bindingError_lifts` performs that translation *once*, at the
      typeclass level. It bounds the joint-experiment probability of
      "the multi-position opening checks AND a designated in-list
      value disagrees with the witness" directly by `bindingError κ q`.
      Downstream theorems can then close their binding-side bounds
      with a single typeclass invocation, supplying only the
      extractors `mkVk … mkValWit` that pick out the relevant
      sub-objects from each experiment outcome.

      ## The seven extractors

      Concretely: given a joint distribution `μ : PMF Ω` and per-
      outcome extractors of
        * a verifier key `mkVk ω`,
        * a commitment `mkCm ω`,
        * an opening `(mkIdxs ω, mkVals ω, mkPrf ω)`,
        * an in-list position `mkLocalIdx ω : ℕ`,
        * a witness value `mkValWit ω`,
      the probability of the joint event
        "the multi-position opening checks AND the in-list value at
         `mkLocalIdx` differs from the witness value (both consulted
         with `getD default`)"
      is at most `bindingError κ q`.

      Concretely: given a joint distribution `μ : PMF Ω` and per-
      outcome extractors of
        * a verifier key `mkVk ω`,
        * a commitment `mkCm ω`,
        * an opening `(mkIdxs ω, mkVals ω, mkPrf ω)`,
        * an in-list position `mkLocalIdx ω : ℕ`,
        * a witness value `mkValWit ω`,
      the probability of the joint event
        "the multi-position opening checks AND the in-list value at
         `mkLocalIdx` differs from the witness value (both consulted
         with `getD default`)"
      is at most `bindingError κ q`.

      The 'witness' value carries an implicit existential proof — the
      validated sample that placed `mkValWit ω` at the position
      `mkIdxs ω |>.getD (mkLocalIdx ω) _` during the experiment has,
      by construction, a VC-check-passing opening proof for that
      `(cm, position, mkValWit ω)`. The field abstracts that witness
      proof away rather than requiring the protocol theorem to thread
      it explicitly.

      ## How to discharge for a concrete VC

      A concrete `instance : HasPositionBinding V` constructs a
      `BindingAdversary κ q` that:
        1. Runs the joint experiment `μ` (using the simulator's RO if
           in the ROM, or the supplied randomness otherwise).
        2. Extracts the witness-side proof from the sampler transcript
           of whichever earlier round placed `mkValWit ω` into the
           candidate string at the relevant position.
        3. Reduces the multi-position `check` predicate to the
           single-position check expected by `BindingBreak`, via a
           VC-specific structural lemma (for Merkle commitments: the
           sibling-path uniqueness lemma).
        4. Packages the two openings into a `BindingBreak V` and
           invokes `binding_bound`. -/
  bindingError_lifts :
    ∀ {κ q : ℕ} {Ω : Type} [Inhabited (VectorCommitment.Alphabet V)]
      (μ : PMF Ω)
      (mkVk : Ω → VectorCommitment.VerifierKey V)
      (mkCm : Ω → VectorCommitment.Commitment V)
      (mkIdxs : Ω → List (VectorCommitment.Index V))
      (mkVals : Ω → List (VectorCommitment.Alphabet V))
      (mkPrf : Ω → VectorCommitment.Proof V)
      (mkLocalIdx : Ω → ℕ)
      (mkValWit : Ω → VectorCommitment.Alphabet V),
      μ.toOuterMeasure
        {ω | VectorCommitment.check (mkVk ω) (mkCm ω)
               (mkIdxs ω) (mkVals ω) (mkPrf ω) = true ∧
             ((mkVals ω)[mkLocalIdx ω]?).getD default ≠ mkValWit ω}
        ≤ bindingError κ q
