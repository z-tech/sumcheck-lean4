/-
Copyright (c) 2026 LeanStuff contributors. All rights reserved.
-/
import Kilian.Properties.Adversary
import Kilian.Properties.Reductor
import Kilian.Properties.Lemma53
import PCP.Src.Security.Soundness
import VectorCommitment.Src.Security.PositionBinding

/-!
# Theorem 5.1 — soundness of Kilian's protocol

Statement of the main soundness theorem from
[eprint 2024/1434, *Untangling the Security of Kilian's Protocol*](https://eprint.iacr.org/2024/1434)
(Chiesa, Dall'Agnol, Guan, Spooner, Yogev), Section 5.

## The theorem

For a PCP `P` with soundness error `ε_PCP(n)` and proof length `ℓ(n)`,
and a vector commitment `V` with position-binding error `ε_VC(κ, q)`,
Kilian's compiled 3-message argument satisfies, for every adversary `A`
and every `ε > 0`:

  argumentError A pp vk n ≤ ε_PCP(n) + ε_VC(κ, q) + ε.

The `argumentError` quantity is defined in
[`Kilian/Properties/Adversary.lean`](Adversary.lean) as the probability
of the standard soundness experiment: `A` chooses a size-`≤ n`
statement `x` outside the language, then runs the 3-message protocol
against the honest verifier; the bound caps the probability that the
verifier accepts.

## Proof structure (per 2024/1434, §5.1–§5.2)

1. **The reductor `R` (Construction 5.5).** Given an argument prover
   `A`, the reductor samples `N = ℓ/ε` independent verifier challenges,
   runs `A`'s response phase on each, and post-processes the resulting
   transcripts into a single candidate PCP string `Π̃`. (See
   [`Kilian/Properties/Reductor.lean`](Reductor.lean).)

2. **Lemma 5.3** (the technical core). Bound the probability of the bad
   event `B = {Π̃ rejects ∧ argument accepts ∧ VC openings check}` by
   `ε_VC(κ, q) + ε`. Two subcases:

   * **`q ∈ Q ∩ Q̃` with disagreeing answers.** The argument prover
     and the reductor's witness disagree on the value at some queried
     position both of them sampled. The disagreement, together with
     both openings checking under `V.check`, is a position-binding
     break — bounded by `bindingError κ q` via `[HasPositionBinding V]`.

   * **`q ∈ Q \ Q̃`** (the verifier queried a position the reductor
     never saw). Bounded by `ℓ/N = ε` via the elementary inequality
     `δ · (1 - δ)^N ≤ 1/N` and a union bound over `ℓ` positions.

3. **Total probability decomposition.**

       Pr[arg accepts ∧ x ∉ L]
         = Pr[arg accepts ∧ PCP-V accepts on Π̃]
         + Pr[arg accepts ∧ PCP-V rejects on Π̃]
         ≤ ε_PCP(n) + Lemma 5.3.

   Yielding the claimed bound.

## Status

The theorem is fully proved (no `sorry`, no extra axioms beyond
`propext`, `Classical.choice`, `Quot.sound` — the standard Mathlib
foundation). It binds abstractly on `[HasPositionBinding V]` and
`[HasSoundness P]`, so the `bindingError` and `soundnessError`
summands are *real values* the moment concrete model instances are
plugged in.

## What the theorem assumes

In addition to the typeclasses, `kilian_soundness` takes three narrow
hypotheses that abstract the "real cryptographic content" of the
analysis. A concrete instantiation must discharge each:

| Hypothesis        | What it says                                          | How to discharge                                                                              |
|-------------------|-------------------------------------------------------|-----------------------------------------------------------------------------------------------|
| `hwf`             | `verifyTranscript` rejects length-mismatched replies. | Inspect the concrete `verifyTranscript`; this holds for any verifier that gates on length.   |
| `h_queries_bound` | `PCPSystem.verifierQueries` only produces indices in `[ℓ]`.  | Follows from the concrete PCP's `proofLength`-bounded query function.                  |
| `h_per_pos`       | Per-position missing-probability is at most `1/N`.   | Standard probability: independence of `ρ` and `rhos`, i.i.d. `rhos`, plus the elementary inequality `δ(1-δ)^N ≤ 1/N` proved in [`PCP/Probability.lean`](../../PCP/Probability.lean). |

These hypotheses *exist* because the abstract experiment is parameterised
on an arbitrary `rhosDist : PMF (List (Randomness P))`; the bounds only
hold when `rhosDist` is the N-fold i.i.d. of `randomnessDist`, which the
caller asserts via `h_per_pos`.

The position-binding side is similarly model-neutral: `bound_case1`
discharges via `HasPositionBinding.bindingError_lifts` (a typeclass
field that lifts position-binding to joint distributions; see the field's
docstring for the design rationale).
-/

open MeasureTheory

-- Same rationale as in `Lemma53.lean`: the section's
-- `[HasPositionBinding V]` instance is needed by `kilian_soundness`
-- (which invokes `bound_case1`'s closure transitively) but not by every
-- sub-lemma in this file. Disable the unused-section-vars linter rather
-- than splitting the section.
set_option linter.unusedSectionVars false

namespace Kilian

variable {P V : Type} [PCPSystem P] [Inhabited (PCPSystem.Alphabet P)]
  [HasSoundness P] [VectorCommitment V] [HasPositionBinding V]
  [KilianCompatible P V] {spec : OracleSpec}

/-! ## Sub-lemmas of the total-probability decomposition.

The proof of `kilian_soundness` is a calc chain on top of three
sub-lemmas — each fully proved — that together implement the §5.2
decomposition:

* `argumentError_split` — total probability: split the argument-win
  event by whether the PCP verifier accepts on the reductor's `Π̃`.
* `bound_pcp_case` — the "PCP accepts on Π̃" half is bounded by
  `HasSoundness.soundnessError n`. Uses `HasSoundness.soundness_bound`
  on `Π̃` plus `HasSoundness.soundnessError_mono` to lift the per-x
  bound to `soundnessError n` when the statement size is `≤ n`.
* `Lemma53.lemma53` — the "PCP rejects on Π̃" half is bounded by
  `ε_VC + ε`. Lives in [`Lemma53.lean`](Lemma53.lean); decomposes
  further into `bound_case1` (binding via `bindingError_lifts`) and
  `bound_case2` (missing-positions via union bound + per-position
  hypothesis).
-/

/-- The PCP-acceptance half of the total-probability split: probability
    that `A` chose a non-instance of size ≤ `n` AND the PCP verifier
    accepts on the reductor's candidate `Π̃`. Bounded by
    `HasSoundness.soundnessError n`. -/
def pcpAcceptsEvent (vk : VectorCommitment.VerifierKey V) (n : ℕ)
    (e : Lemma53.Experiment P V) : Prop :=
  HasSoundness.statementSize (P := P) e.statement ≤ n ∧
  ¬ PCPSystem.language P e.statement ∧
  Kilian.verifyTranscript e.statement vk e.transcript = true ∧
  -- PCP verifier accepts on reductor's Π̃ at this transcript's ρ:
  PCPSystem.verifierDecide (P := P) e.statement e.transcript.randomness
      (PCPSystem.readAt (P := P) e.pi_tilde
        (PCPSystem.verifierQueries (P := P) e.statement e.transcript.randomness)
        default) = true

/-- The well-formedness property the argument verifier is assumed to
    enforce: if it accepts, the reply length matches the query count.

    Every sensible PCP-VC instantiation has this property (the verifier
    rejects malformed replies before invoking `verifierDecide`). We
    factor it out as an explicit hypothesis so the soundness theorem is
    parameterised on the assumption, rather than baking it into a
    typeclass field. -/
def WellFormedVerifier (vk : VectorCommitment.VerifierKey V) : Prop :=
  ∀ (x : PCPSystem.Statement P) (t : Transcript P V),
    Kilian.verifyTranscript x vk t = true →
    t.values.length = (PCPSystem.verifierQueries (P := P) x t.randomness).length

/-- **Total-probability decomposition.**

    The `argumentError` set `{statementSize ≤ n ∧ ¬language ∧ argument
    accepts}` is contained in the union of `pcpAcceptsEvent` (PCP
    verifier accepts on the reductor's `Π̃`) and `isBad` (PCP verifier
    rejects on `Π̃`). The split is a clean case-analysis on the PCP
    verifier's Boolean output at `(x, ρ)` reading `Π̃`, using
    `WellFormedVerifier` to discharge the length-match conjunct of
    `isBad` from the assumption that the argument verifier accepted.

    Proof: set containment by Boolean case split + outer-measure
    monotonicity + subadditivity on union. -/
theorem argumentError_split
    (A : Adversary P V spec)
    (pp : VectorCommitment.UniversalParams V)
    (vk : VectorCommitment.VerifierKey V)
    (n ℓ : ℕ)
    (rhosDist : PMF (List (PCPSystem.Randomness P)))
    (hwf : WellFormedVerifier (P := P) (V := V) vk) :
    Lemma53.argumentError A pp vk n ℓ rhosDist ≤
      (Lemma53.experiment A pp vk ℓ rhosDist).toOuterMeasure
        {e | pcpAcceptsEvent vk n e}
      +
      (Lemma53.experiment A pp vk ℓ rhosDist).toOuterMeasure
        {e | Lemma53.isBad vk e} := by
  -- Set containment: argumentError's set ⊆ pcpAccepts ∪ isBad.
  have hsub :
      {e : Lemma53.Experiment P V |
         HasSoundness.statementSize (P := P) e.statement ≤ n ∧
         ¬ PCPSystem.language P e.statement ∧
         Kilian.verifyTranscript e.statement vk e.transcript = true} ⊆
      {e | pcpAcceptsEvent vk n e} ∪ {e | Lemma53.isBad vk e} := by
    intro e he
    obtain ⟨hsize, hnotL, hvt⟩ := he
    -- Case split on whether the PCP verifier accepts on Π̃.
    by_cases h :
        PCPSystem.verifierDecide (P := P) e.statement
            e.transcript.randomness
            (PCPSystem.readAt (P := P) e.pi_tilde
              (PCPSystem.verifierQueries (P := P) e.statement
                e.transcript.randomness) default) = true
    · -- PCP V accepts: e ∈ pcpAcceptsEvent.
      exact Or.inl ⟨hsize, hnotL, hvt, h⟩
    · -- PCP V rejects: e ∈ isBad. Length-match comes from WellFormedVerifier.
      have h_len : e.transcript.values.length =
          (PCPSystem.verifierQueries (P := P) e.statement
            e.transcript.randomness).length :=
        hwf e.statement e.transcript hvt
      refine Or.inr ⟨h_len, ?_, hvt⟩
      exact (Bool.not_eq_true _).mp h
  -- Outer measure: monotone + subadditive on union.
  calc Lemma53.argumentError A pp vk n ℓ rhosDist
      = (Lemma53.experiment A pp vk ℓ rhosDist).toOuterMeasure
          {e | HasSoundness.statementSize (P := P) e.statement ≤ n ∧
               ¬ PCPSystem.language P e.statement ∧
               Kilian.verifyTranscript e.statement vk e.transcript = true} :=
        rfl
    _ ≤ (Lemma53.experiment A pp vk ℓ rhosDist).toOuterMeasure
          ({e | pcpAcceptsEvent vk n e} ∪ {e | Lemma53.isBad vk e}) :=
        measure_mono hsub
    _ ≤ (Lemma53.experiment A pp vk ℓ rhosDist).toOuterMeasure
          {e | pcpAcceptsEvent vk n e}
        + (Lemma53.experiment A pp vk ℓ rhosDist).toOuterMeasure
          {e | Lemma53.isBad vk e} :=
        measure_union_le _ _

/-! ### Helper: pointwise bound on a binded PMF lifts to a uniform bound.

    If for every value `a : α` the conditional `(f a).toOuterMeasure s`
    is bounded by `C`, then the unconditional outer measure of `s` under
    `p.bind f` is also bounded by `C`. This is the basic "integrate the
    pointwise bound" step; it lets us bound the deeply-nested
    `experiment` PMF in `bound_pcp_case` by peeling off binds from the
    outside in.

    Proof: `PMF.toOuterMeasure_bind_apply` gives the tsum, then bound
    each summand by `p a * C` and pull out the constant; `PMF.tsum_coe`
    closes the resulting `(∑ p a) * C = 1 * C = C`. -/
private lemma pmf_bind_toOuterMeasure_le {α β : Type}
    (p : PMF α) (f : α → PMF β) (s : Set β) (C : ENNReal)
    (h : ∀ a, (f a).toOuterMeasure s ≤ C) :
    (p.bind f).toOuterMeasure s ≤ C := by
  rw [PMF.toOuterMeasure_bind_apply]
  calc ∑' a, p a * (f a).toOuterMeasure s
      ≤ ∑' a, p a * C :=
        ENNReal.tsum_le_tsum (fun a => by gcongr; exact h a)
    _ = (∑' a, p a) * C := ENNReal.tsum_mul_right
    _ = 1 * C := by rw [PMF.tsum_coe]
    _ = C := one_mul _

/-! ### Helper: change-of-variables bound.

    If `g : α → β` factors a property `s` of `β` through a property `t`
    of `α` (i.e., `g a ∈ s` iff `a ∈ t`), then the outer measure of `s`
    under any `p.bind (fun a => q a)` with each `q a` supported on
    elements `b` satisfying `g a ∈ s ↔ b ∈ s` reduces to the outer
    measure of `t` under `p`. Statement-light variant: bound the binded
    measure by `p.toOuterMeasure t`. -/
private lemma pmf_bind_toOuterMeasure_le_of_subevent
    {α β : Type} (p : PMF α) (f : α → PMF β) (s : Set β) (t : Set α)
    (h : ∀ a, (f a).toOuterMeasure s ≤ t.indicator (fun _ => (1 : ENNReal)) a) :
    (p.bind f).toOuterMeasure s ≤ p.toOuterMeasure t := by
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply]
  calc ∑' a, p a * (f a).toOuterMeasure s
      ≤ ∑' a, p a * t.indicator (fun _ => (1 : ENNReal)) a :=
        ENNReal.tsum_le_tsum (fun a => by gcongr; exact h a)
    _ = ∑' a, t.indicator p a := by
        refine tsum_congr (fun a => ?_)
        by_cases ha : a ∈ t
        · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha, mul_one]
        · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha, mul_zero]

/-- **PCP-acceptance bound.** When the PCP verifier accepts on the
    reductor's candidate string `Π̃` at `(x, ρ)`, the soundness of the
    underlying PCP bounds the probability by `ε_PCP(n)` — independently
    of whether the argument verifier accepts.

    Proof: enlarge the event by dropping the `verifyTranscript` conjunct
    (`measure_mono`). The remaining event only depends on `x`,
    `Π̃ = e.pi_tilde`, and `ρ = e.transcript.randomness`, not on the
    response-phase reply. We peel the experiment's binds from the
    outside in via `pmf_bind_toOuterMeasure_le`, fixing `x` and `Π̃` at
    the `(commitPhase, reductor)` layer. At the inner layer (with
    `(x, Π̃)` fixed), the remaining `randomnessDist >>= ρ; …; pure`
    block has outer measure bounded by
    `randomnessDist.toOuterMeasure {ρ | V accepts on Π̃ at (x, ρ)}` —
    by definition `PCPSystem.acceptanceProb x Π̃`. For `x ∉ L` with
    `size x ≤ n`, `HasSoundness.soundness_bound` bounds this by
    `soundnessError (statementSize x)`, and
    `HasSoundness.soundnessError_mono` lifts to `soundnessError n`. -/
theorem bound_pcp_case
    (A : Adversary P V spec)
    (pp : VectorCommitment.UniversalParams V)
    (vk : VectorCommitment.VerifierKey V)
    (n ℓ : ℕ)
    (rhosDist : PMF (List (PCPSystem.Randomness P))) :
    (Lemma53.experiment A pp vk ℓ rhosDist).toOuterMeasure
        {e | pcpAcceptsEvent vk n e}
      ≤ HasSoundness.soundnessError (P := P) n := by
  -- Step 1: drop the `verifyTranscript` conjunct of the event.
  set s : Set (Lemma53.Experiment P V) :=
      {e |
        HasSoundness.statementSize (P := P) e.statement ≤ n ∧
        ¬ PCPSystem.language P e.statement ∧
        PCPSystem.verifierDecide (P := P) e.statement e.transcript.randomness
          (PCPSystem.readAt (P := P) e.pi_tilde
            (PCPSystem.verifierQueries (P := P) e.statement
              e.transcript.randomness) default) = true} with hs_def
  have hsub : {e | pcpAcceptsEvent vk n e} ⊆ s := by
    intro e he
    obtain ⟨h1, h2, _, h4⟩ := he
    exact ⟨h1, h2, h4⟩
  refine (measure_mono hsub).trans ?_
  -- Step 2: peel binds. The experiment is a chain of binds ending in `pure {…}`.
  unfold Lemma53.experiment
  -- Outer layer: η ← auxDist.
  refine pmf_bind_toOuterMeasure_le _ _ _ _ (fun η => ?_)
  -- phase1 ← simulateQ (commitPhase pp η).
  refine pmf_bind_toOuterMeasure_le _ _ _ _ (fun phase1 => ?_)
  -- rhos ← rhosDist.
  refine pmf_bind_toOuterMeasure_le _ _ _ _ (fun rhos => ?_)
  -- out ← simulateQ (Reductor.reduce …).
  refine pmf_bind_toOuterMeasure_le _ _ _ _ (fun out => ?_)
  -- Fix x := phase1.1 and π̃ := out.pi.
  set x : PCPSystem.Statement P := phase1.1 with hx
  set piT : List (PCPSystem.Alphabet P) := out.pi with hpiT
  -- Step 3: case on whether (size x ≤ n ∧ ¬ language x).
  by_cases hxcond :
      HasSoundness.statementSize (P := P) x ≤ n ∧ ¬ PCPSystem.language P x
  · -- Good case. Bound by `acceptanceProb x piT ≤ soundnessError n`.
    -- The remainder is `do ρ ← randomnessDist; reply ← simulateQ(...); pure {...}`.
    -- We claim this is bounded by `randomnessDist.toOuterMeasure acceptSet`, where
    -- `acceptSet := {ρ | V accepts on piT at (x, ρ)}`. That equals `acceptanceProb x piT`.
    -- Use `pmf_bind_toOuterMeasure_le_of_subevent` on the outer ρ-bind, with
    -- t := acceptSet. For each ρ, the inner `reply ← ...; pure {...}` is a pure-bind
    -- whose support is the singleton {ρ ∈ acceptSet ↔ result ∈ s}.
    set acceptSet : Set (PCPSystem.Randomness P) :=
      {ρ' : PCPSystem.Randomness P |
        PCPSystem.verifierDecide (P := P) x ρ'
          (PCPSystem.readAt (P := P) piT
            (PCPSystem.verifierQueries (P := P) x ρ') default) = true} with hAccept
    have h_ρ_le :
        ((PCPSystem.randomnessDist (P := P)).bind
            (fun ρ => (OracleComp.simulateQ (A.responsePhase phase1.2.2 ρ)).bind
              (fun reply : List (PCPSystem.Alphabet P) × VectorCommitment.Proof V =>
                PMF.pure
                  ({ statement := x,
                     commitment := phase1.2.1,
                     pi_tilde := piT,
                     covered := out.covered,
                     transcript :=
                       { commitment := phase1.2.1,
                         randomness := ρ,
                         values := reply.1,
                         proof := reply.2 } } : Lemma53.Experiment P V)))).toOuterMeasure s ≤
          (PCPSystem.randomnessDist (P := P)).toOuterMeasure acceptSet := by
      refine pmf_bind_toOuterMeasure_le_of_subevent _ _ _ acceptSet (fun ρ => ?_)
      -- Inner: bind over reply into pure.
      refine pmf_bind_toOuterMeasure_le _ _ _ _ (fun reply => ?_)
      rw [PMF.toOuterMeasure_pure_apply]
      -- Goal: `(if pureElt ∈ s then 1 else 0) ≤ acceptSet.indicator (fun _ => 1) ρ`.
      by_cases hin :
          ({ statement := x,
             commitment := phase1.2.1,
             pi_tilde := piT,
             covered := out.covered,
             transcript :=
               { commitment := phase1.2.1,
                 randomness := ρ,
                 values := reply.1,
                 proof := reply.2 } } : Lemma53.Experiment P V) ∈ s
      · rw [if_pos hin]
        have h_in_accept : ρ ∈ acceptSet := hin.2.2
        rw [Set.indicator_of_mem h_in_accept]
      · rw [if_neg hin]
        exact zero_le _
    refine le_trans h_ρ_le ?_
    -- Bound `acceptanceProb x piT` by `soundnessError (statementSize x)` then by `soundnessError n`.
    have h_eq : (PCPSystem.randomnessDist (P := P)).toOuterMeasure acceptSet
              = PCPSystem.acceptanceProb (P := P) x piT := rfl
    rw [h_eq]
    refine le_trans (HasSoundness.soundness_bound x hxcond.2 piT) ?_
    exact HasSoundness.soundnessError_mono hxcond.1
  · -- Bad case: integrate; the indicator is 0 because every pure outcome has
    -- statement = x with the size/language conditions failing.
    refine pmf_bind_toOuterMeasure_le _ _ _ _ (fun ρ => ?_)
    refine pmf_bind_toOuterMeasure_le _ _ _ _ (fun reply => ?_)
    -- The `have values := reply.1; have proof := reply.2; pure {…}` desugars to
    -- `pure {…[reply.1, reply.2]}`. Use `show` to rewrite to an explicit `PMF.pure`.
    show ((PMF.pure
        ({ statement := x,
           commitment := phase1.2.1,
           pi_tilde := piT,
           covered := out.covered,
           transcript :=
             { commitment := phase1.2.1,
               randomness := ρ,
               values := reply.1,
               proof := reply.2 } } : Lemma53.Experiment P V))
        : PMF (Lemma53.Experiment P V)).toOuterMeasure s ≤
      HasSoundness.soundnessError (P := P) n
    rw [PMF.toOuterMeasure_pure_apply]
    have hnotin :
        ({ statement := x,
           commitment := phase1.2.1,
           pi_tilde := piT,
           covered := out.covered,
           transcript :=
             { commitment := phase1.2.1,
               randomness := ρ,
               values := reply.1,
               proof := reply.2 } } : Lemma53.Experiment P V) ∉ s := by
      intro h
      exact hxcond ⟨h.1, h.2.1⟩
    rw [if_neg hnotin]
    exact zero_le _

/-- **Theorem 5.1 of [eprint 2024/1434].**

    Kilian's compiled argument from a PCP `P` and a vector commitment
    `V` has soundness error bounded by `ε_PCP(n) + ε_VC(κ, q) + ε`
    for every statement-size bound `n`, VC security parameter `κ`,
    VC adversary budget `q`, and slack `ε > 0`.

    The bound binds on `[HasPositionBinding V]` (sources `ε_VC`) and
    `[HasSoundness P]` (sources `ε_PCP`) abstractly, so each summand is
    a real model-instantiated value (ROM, standard-model CR, …) at the
    use site.

    Proof: total-probability decomposition (`argumentError_split`),
    then bound each half by `bound_pcp_case` and `Lemma53.lemma53`.

    ## Hypotheses (the "narrow assumptions")

    Beyond the typeclasses, three explicit hypotheses package the real
    cryptographic content that the abstract theorem can't see:

    * `h_eps : ε = ℓ / N` — pins the slack `ε` to the reductor's
      `N`-sample budget. Caller chooses `N := ⌈ℓ/ε⌉` for a given target
      `ε`.

    * `hwf : WellFormedVerifier vk` — the argument verifier rejects
      any reply whose answer list doesn't match the query count. Holds
      for every protocol that gates on length; see the docstring of
      `WellFormedVerifier`.

    * `h_queries_bound` — the PCP verifier's query function only emits
      indices `< ℓ`. Follows from the concrete PCP's `proofLength`
      contract.

    * `h_per_pos` — for each position `q < ℓ`, the marginal probability
      "verifier picks `q` AND the reductor's `rhos` never cover `q`"
      is at most `1/N`. This is the per-position content of the paper's
      missing-positions analysis: under independence `ρ ⊥ rhos` and
      i.i.d. `rhos ∼ randomnessDist^N`, it factors as `δ_q · (1-δ_q)^N`
      and the elementary inequality `δ(1-δ)^N ≤ 1/N` (proved in
      [`PCP.Probability.delta_compl_pow_le`](../../PCP/Probability.lean))
      closes it.

    All four are *standard* assumptions about a deployed PCP+VC stack;
    the abstract theorem makes them explicit. When instantiating
    `kilian_soundness` for a concrete `(PCPSystem, VectorCommitment)`
    pair plus a concrete `rhosDist`, the caller discharges them. -/
theorem kilian_soundness
    (A : Adversary P V spec)
    (pp : VectorCommitment.UniversalParams V)
    (vk : VectorCommitment.VerifierKey V)
    (κ q n ℓ N : ℕ) (ε : ENNReal)
    (rhosDist : PMF (List (PCPSystem.Randomness P)))
    (h_eps : ε = (ℓ : ENNReal) / (N : ENNReal))
    (hwf : WellFormedVerifier (P := P) (V := V) vk)
    (h_queries_bound : ∀ (x : PCPSystem.Statement P)
        (ρ : PCPSystem.Randomness P),
      ∀ q ∈ PCPSystem.verifierQueries (P := P) x ρ, q < ℓ)
    (h_per_pos : ∀ q : ℕ, q < ℓ →
        (Lemma53.experiment A pp vk ℓ rhosDist).toOuterMeasure
          {e | q ∈ PCPSystem.verifierQueries (P := P) e.statement
                     e.transcript.randomness ∧
               q ∉ e.covered}
        ≤ (1 : ENNReal) / N) :
    Lemma53.argumentError A pp vk n ℓ rhosDist ≤
      HasSoundness.soundnessError (P := P) n +
      HasPositionBinding.bindingError (V := V) κ q + ε := by
  calc Lemma53.argumentError A pp vk n ℓ rhosDist
      ≤ (Lemma53.experiment A pp vk ℓ rhosDist).toOuterMeasure
            {e | pcpAcceptsEvent vk n e}
        + (Lemma53.experiment A pp vk ℓ rhosDist).toOuterMeasure
            {e | Lemma53.isBad vk e} := by
          exact argumentError_split A pp vk n ℓ rhosDist hwf
    _ ≤ HasSoundness.soundnessError (P := P) n
        + (HasPositionBinding.bindingError (V := V) κ q + ε) := by
          exact add_le_add
            (bound_pcp_case A pp vk n ℓ rhosDist)
            (Lemma53.lemma53 A pp vk ℓ N rhosDist κ q ε h_eps
              h_queries_bound h_per_pos)
    _ = HasSoundness.soundnessError (P := P) n
        + HasPositionBinding.bindingError (V := V) κ q + ε := by
          rw [add_assoc]

end Kilian
