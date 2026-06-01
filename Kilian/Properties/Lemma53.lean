/-
Copyright (c) 2026 LeanStuff contributors. All rights reserved.
-/
import Kilian.Properties.Reductor
import VectorCommitment.Src.Security.PositionBinding
import Mathlib.Data.List.GetD

/-!
# Lemma 5.3 — the technical core of Theorem 5.1

> *Statement (informal).* For every `ε > 0`, every adversary `A` against
> the Kilian-compiled argument, and every aux-input distribution, the
> probability of the joint event
>
>   * `V^{[Q̃, Π̃]}(x; ρ) = 0`   — the PCP verifier rejects on the
>     reductor's candidate PCP string `Π̃`;
>   * `V^{[Q, ans]}(x; ρ) = 1` — the argument verifier's PCP-check
>     accepts on the adversary's reply;
>   * `VC.Check(pp, cm, Q, ans, pf) = 1` — the argument verifier's VC
>     check accepts on the adversary's reply
>
> is at most `ε_VC(λ, ℓ, q, t_VC) + ε`, where the reductor `R` produces
> `(Q̃, Π̃)` from `A.responsePhase` by `N := ⌈ℓ/ε⌉` rewinds.

This is the engine of Theorem 5.1. The two cases in the proof are:

1. **Disagreeing answers** at a position `q ∈ Q ∩ Q̃` — bounded by the
   VC's position-binding error `ε_VC` via `[HasPositionBinding V]`.

2. **Missing positions** `q ∈ Q \ Q̃` (the verifier queries a position
   the reductor never saw) — bounded by `ℓ/N = ε` via a union bound
   over `[ℓ]` and the elementary inequality `δ·(1-δ)^N ≤ 1/N`.

The two cases are combined by a final union bound.

In our framework the queried-position set `Q` is deterministic from
`(x, ρ)` (re-derived by both the honest verifier and the reductor via
`PCPSystem.verifierQueries`), so the "disagreeing answers" case
collapses to: for some `q ∈ Q`, the value `ans` reports differs from
`Π̃[q]` while VC.Check passes.

## References

* Chiesa, Dall'Agnol, Guan, Spooner, Yogev,
  *Untangling the Security of Kilian's Protocol*,
  [eprint 2024/1434](https://eprint.iacr.org/2024/1434),
  Lemma 5.3 (§5.1).
-/

open MeasureTheory

-- The `[HasSoundness P]` and `[HasPositionBinding V]` instances in
-- the section variables below are not all needed by every theorem in
-- this file (the case lemmas don't touch the other typeclass), but
-- carrying them in the section keeps signatures aligned with `lemma53`
-- and `kilian_soundness`. Disable the unused-section-vars linter to
-- silence the cosmetic warnings.
set_option linter.unusedSectionVars false

namespace Kilian

namespace Lemma53

variable {P V : Type} [PCPSystem P] [Inhabited (PCPSystem.Alphabet P)]
  [HasSoundness P] [VectorCommitment V] [HasPositionBinding V]
  [KilianCompatible P V] {spec : OracleSpec}

/-- A general fact: for any type equality `h : α = β`, `h ▸ a = h ▸ b`
    iff `a = b`. (The `▸` cast is injective.) -/
private lemma cast_eq_iff.{u} {α β : Type u} (h : α = β) (a b : α) :
    (h ▸ a : β) = h ▸ b ↔ a = b := by
  subst h; rfl

/-- The corresponding ≠ version. -/
private lemma cast_ne_iff.{u} {α β : Type u} (h : α = β) (a b : α) :
    (h ▸ a : β) ≠ h ▸ b ↔ a ≠ b := by
  rw [ne_eq, ne_eq, cast_eq_iff]

/-- Indexing a list cast through a type-level equality commutes with
    casting through that equality:
    `(h ▸ xs)[i]?.getD d = h ▸ (xs[i]?.getD d')`
    when `d` is pre-cast from `d'`. -/
private lemma cast_list_getElem?_getD.{u}
    {α β : Type u} (h : α = β) (xs : List α) (i : ℕ) (d : α) :
    ((h ▸ xs : List β)[i]?).getD (h ▸ d) = (h ▸ ((xs[i]?).getD d) : β) := by
  subst h; rfl

/-- A single outcome of the Lemma-5.3 experiment, packaging the pieces
    we want to predicate on:
      * `x`            — the statement chosen by the adversary's commit phase.
      * `cm`           — the VC commitment chosen by the adversary.
      * `pi_tilde`     — the reductor's candidate PCP string.
      * `covered`      — the set `Q̃` of positions the reductor filled.
      * `transcript`   — the adversary's reply on a fresh challenge `ρ`.
    Held as a structure so the bad-event predicate reads naturally. -/
structure Experiment (P V : Type) [PCPSystem P] [VectorCommitment V] where
  statement     : PCPSystem.Statement P
  commitment    : VectorCommitment.Commitment V
  pi_tilde      : List (PCPSystem.Alphabet P)
  covered       : List ℕ
  transcript    : Transcript P V

/-- The bad event: the adversary's reply is *well-formed* (its length
    matches the verifier's query budget), the PCP verifier *rejects*
    on the reductor's candidate `Π̃` at `(x, ρ)`, and the Kilian
    verifier accepts on the adversary's reply at the same `(x, ρ)`.

    The well-formedness conjunct is harmless: any sensible argument
    verifier rejects answer lists whose length doesn't match the query
    count, so this just restricts `isBad` to the realisations the
    soundness analysis actually cares about. See `argumentError_split`
    in [`Theorem51.lean`](../Theorem51.lean) for the precise
    propagation. -/
def isBad (vk : VectorCommitment.VerifierKey V) (e : Experiment P V) : Prop :=
  let ρ := e.transcript.randomness
  let queriesOn_ρ := PCPSystem.verifierQueries (P := P) e.statement ρ
  -- Well-formedness: the adversary supplied exactly one answer per query.
  e.transcript.values.length = queriesOn_ρ.length
  ∧
  -- PCP verifier rejects on reductor's Π̃:
  (PCPSystem.verifierDecide (P := P) e.statement ρ
      (PCPSystem.readAt (P := P) e.pi_tilde queriesOn_ρ default) = false)
  ∧
  -- Argument verifier accepts on adversary's transcript:
  Kilian.verifyTranscript e.statement vk e.transcript = true

/-- The full experiment of Lemma 5.3, as a `PMF` over `Experiment`
    outcomes:

      η     ← A.auxDist
      (x, cm, aux) ← A.commitPhase(pp, η)       -- RO inside
      rhos  ← rhosDist                          -- N fresh PCP challenges
      out   ← R(A, vk, x, cm, aux, rhos, ℓ)     -- reductor (RO inside)
      ρ     ← PCPSystem.randomnessDist          -- fresh verifier coin
      (ans, pf) ← A.responsePhase(aux, ρ)       -- RO inside

    The caller picks `rhosDist` (typically `(PCPSystem.randomnessDist)^N`
    for `N := ⌈ℓ/ε⌉`); leaving it abstract here keeps the lemma
    parameterised on `(N, ε)` choice. -/
noncomputable def experiment
    (A : Adversary P V spec)
    (pp : VectorCommitment.UniversalParams V)
    (vk : VectorCommitment.VerifierKey V)
    (ℓ : ℕ)
    (rhosDist : PMF (List (PCPSystem.Randomness P))) :
    PMF (Experiment P V) := do
  let η ← A.auxDist
  let phase1 ← OracleComp.simulateQ (A.commitPhase pp η)
  let x   := phase1.1
  let cm  := phase1.2.1
  let aux := phase1.2.2
  let rhos ← rhosDist
  let out  ← OracleComp.simulateQ (Reductor.reduce A vk x cm aux rhos ℓ)
  let ρ ← PCPSystem.randomnessDist (P := P)
  let reply ← OracleComp.simulateQ (A.responsePhase aux ρ)
  let values := reply.1
  let proof  := reply.2
  pure {
    statement   := x,
    commitment  := cm,
    pi_tilde    := out.pi,
    covered     := out.covered,
    transcript  := { commitment := cm,
                     randomness := ρ,
                     values     := values,
                     proof      := proof } }

/-! ## Case split

The bad event `isBad` decomposes (paper §5.1) into two sub-events on
the same experiment outcome:

* `disagreeingAnswers` — there is a position `q ∈ Q ∩ Q̃` where the
  adversary's reported value differs from `Π̃[q]`. The VC openings on
  both sides check, so this is a position-binding break.

* `missingPosition` — there is a position `q ∈ Q \ Q̃`, i.e. the
  verifier queries something the reductor never touched.

The bad event is contained in the union: every realisation in `isBad`
must satisfy one of the two (because the joint event of "PCP rejects
on Π̃" while "argument accepts" requires either the prover lied at a
covered position or queried an uncovered position).
-/

/-- The Case-1 sub-event: at some queried index `i` (i.e.
    `i < (verifierQueries x ρ).length`), the position `q := queries[i]`
    is covered by the reductor *and* the adversary's reported value at
    `i` differs from `Π̃[q]`. The Option-based comparison
    (`getD default`) naturally folds length mismatches between
    `values` and `queries` into the same "disagreement at this index"
    notion.

    The bundled `verifyTranscript = true` conjunct ensures the
    adversary's VC opening actually checks at this index, which is
    what makes the disagreement a position-binding break (rather than
    a vacuous list mismatch). It is automatically discharged in
    `isBad_subset_cases` from the `isBad`-side `verifyTranscript`
    hypothesis, so adding it does not weaken the case-union
    statement. -/
def disagreeingAnswers (vk : VectorCommitment.VerifierKey V)
    (e : Experiment P V) : Prop :=
  let queries := PCPSystem.verifierQueries (P := P) e.statement
                   e.transcript.randomness
  Kilian.verifyTranscript e.statement vk e.transcript = true ∧
  ∃ i : Fin queries.length,
    queries.get i ∈ e.covered ∧
    (e.transcript.values[i.val]?).getD default ≠
      (e.pi_tilde[queries.get i]?).getD default

/-- The Case-2 sub-event: there is a position `q ∈ Q \ Q̃`, i.e. the
    verifier queries something the reductor never recorded. -/
def missingPosition (e : Experiment P V) : Prop :=
  let queries := PCPSystem.verifierQueries (P := P) e.statement
                   e.transcript.randomness
  ∃ q ∈ queries, q ∉ e.covered

/-! ## `argumentError` — the soundness target

Defined here (rather than in `Adversary.lean`) so it shares the joint
experiment `experiment` with the bad event and the case events. That
sharing lets `argumentError_split` (in
[`Theorem51.lean`](Theorem51.lean)) proceed as a single outer-measure
union/monotonicity argument, without an intervening marginalization
identity.

Mathematically the `ℓ`/`rhosDist` parameters are noise: the verifier's
acceptance event doesn't depend on the reductor's randomness, so this
`argumentError` agrees with the obvious "sample only `(η, ρ, RO)`"
version up to a marginal that is trivially absorbed in the experiment
sequence. We keep them as explicit parameters because doing so makes
all downstream lemmas live in a single sample space.
-/

/-- The Kilian argument's soundness error: probability that the
    adversary `A` (i) chooses a statement of size at most `n` (ii)
    outside the PCP's language (iii) such that the Kilian verifier
    accepts — taken over the joint `experiment` distribution. -/
noncomputable def argumentError
    (A : Adversary P V spec)
    (pp : VectorCommitment.UniversalParams V)
    (vk : VectorCommitment.VerifierKey V)
    (n ℓ : ℕ)
    (rhosDist : PMF (List (PCPSystem.Randomness P))) : ENNReal :=
  (experiment A pp vk ℓ rhosDist).toOuterMeasure
    {e | HasSoundness.statementSize (P := P) e.statement ≤ n ∧
         ¬ PCPSystem.language P e.statement ∧
         Kilian.verifyTranscript e.statement vk e.transcript = true}

/-- **Case 1 bound.** Probability of `disagreeingAnswers` is bounded by
    the VC's position-binding error `ε_VC(κ, q)`.

    Proof. The `disagreeingAnswers` event carries both
    `verifyTranscript = true` (so the adversary's VC opening at every
    queried position checks under `vk`) and a witness position
    `q ∈ Q ∩ Q̃` where the adversary's value differs from the
    reductor's candidate `Π̃[q]`. Since `q ∈ Q̃`, the reductor has
    also obtained a validated VC opening at `q` reading the same
    `Π̃[q]`. These two openings of the same `(cm, q)` with disagreeing
    values are a position-binding break.

    We package the experiment as a joint distribution over outcomes
    that produce `(vk, cm, q, val_adv, val_wit, proof_adv)` and apply
    `HasPositionBinding.bindingError_lifts`. The set inclusion
    `disagreeingAnswers ⊆ {ω | check_passes ∧ val_adv ≠ val_wit}` is
    discharged by selecting the first witnessing index in the
    `disagreeingAnswers` existential, extracting the VC sub-check of
    `verifyTranscript`, and reading off the value disagreement. -/
theorem bound_case1
    (A : Adversary P V spec)
    (pp : VectorCommitment.UniversalParams V)
    (vk : VectorCommitment.VerifierKey V)
    (ℓ : ℕ)
    (rhosDist : PMF (List (PCPSystem.Randomness P)))
    (κ q : ℕ) :
    (experiment A pp vk ℓ rhosDist).toOuterMeasure
        {e | disagreeingAnswers (P := P) (V := V) vk e}
      ≤ HasPositionBinding.bindingError (V := V) κ q := by
  classical
  -- `Inhabited` instance on `Alphabet V` via `letI` (let-instance), so the
  -- value is preserved for definitional unfolding: `default : Alphabet V`
  -- reduces to `alphabet_eq ▸ (default : Alphabet P)`.
  letI hInhV : Inhabited (VectorCommitment.Alphabet V) :=
    ⟨KilianCompatible.alphabet_eq (P := P) (V := V) ▸
      (default : PCPSystem.Alphabet P)⟩
  -- The verifier's query list at each outcome.
  let Qof : Experiment P V → List ℕ := fun e =>
    PCPSystem.verifierQueries (P := P) e.statement e.transcript.randomness
  -- Witnessing in-list index when disagreement holds (junk fallback else).
  let idxOf : Experiment P V → ℕ := fun e =>
    if h : disagreeingAnswers (P := P) (V := V) vk e then
      ((Classical.choose h.2) : Fin (Qof e).length).val
    else 0
  -- Extractors threaded into `bindingError_lifts`.
  let mkVk : Experiment P V → VectorCommitment.VerifierKey V := fun _ => vk
  let mkCm : Experiment P V → VectorCommitment.Commitment V :=
    fun e => e.transcript.commitment
  let mkIdxs : Experiment P V → List (VectorCommitment.Index V) := fun e =>
    KilianCompatible.castIndex (P := P) (V := V) (Qof e)
  let mkVals : Experiment P V → List (VectorCommitment.Alphabet V) := fun e =>
    KilianCompatible.castAlphabet (P := P) (V := V) e.transcript.values
  let mkPrf : Experiment P V → VectorCommitment.Proof V := fun e =>
    e.transcript.proof
  let mkLocalIdx : Experiment P V → ℕ := idxOf
  let mkValWit : Experiment P V → VectorCommitment.Alphabet V := fun e =>
    KilianCompatible.alphabet_eq (P := P) (V := V) ▸
      ((e.pi_tilde[(Qof e).getD (idxOf e) 0]?).getD default)
  -- Inclusion: `disagreeingAnswers vk` is contained in the joint
  -- "VC.check passes ∧ in-list value disagrees" event over `experiment`.
  have hsub :
      {e : Experiment P V | disagreeingAnswers (P := P) (V := V) vk e}
        ⊆ {e : Experiment P V |
              VectorCommitment.check (mkVk e) (mkCm e)
                (mkIdxs e) (mkVals e) (mkPrf e) = true ∧
              ((mkVals e)[mkLocalIdx e]?).getD default ≠ mkValWit e} := by
    intro e he
    have he' : disagreeingAnswers (P := P) (V := V) vk e := he
    have h_vt : Kilian.verifyTranscript e.statement vk e.transcript = true :=
      he.1
    have h_ex := he.2
    have hi_eq : idxOf e = (Classical.choose h_ex).val := by
      show (if h : disagreeingAnswers (P := P) (V := V) vk e then
              ((Classical.choose h.2) : Fin (Qof e).length).val
            else 0) = (Classical.choose h_ex).val
      rw [dif_pos he']
    have hwit := Classical.choose_spec h_ex
    refine ⟨?_, ?_⟩
    · -- VC check from `verifyTranscript`.
      have h1 := h_vt
      simp only [Kilian.verifyTranscript, Bool.and_eq_true] at h1
      exact h1.1
    · -- Value disagreement at the local index, after cast-stripping.
      have hne_pcp := hwit.2
      -- Align `(Qof e).getD …` with `(Qof e).get chooser`.
      have h_idx_eq :
          (Qof e).getD (idxOf e) 0 =
          (Qof e).get (Classical.choose h_ex) := by
        rw [List.get_eq_getElem, hi_eq,
            List.getD_eq_getElem _ _ (Classical.choose h_ex).isLt]
      -- Unfold the let-bindings via show.
      show ((KilianCompatible.castAlphabet (P := P) (V := V)
              e.transcript.values)[idxOf e]?).getD default ≠
           (KilianCompatible.alphabet_eq (P := P) (V := V) ▸
              ((e.pi_tilde[(Qof e).getD (idxOf e) 0]?).getD default))
      rw [h_idx_eq, hi_eq]
      -- Unfold `castAlphabet` to expose the underlying `▸` cast.
      unfold KilianCompatible.castAlphabet
      -- Bridge `default : Alphabet V` (instance-resolved) to
      -- `alphabet_eq ▸ (default : Alphabet P)` via the local `hInhV`
      -- instance, which makes them definitionally equal.
      have hdv : (default : VectorCommitment.Alphabet V) =
          KilianCompatible.alphabet_eq (P := P) (V := V) ▸
            (default : PCPSystem.Alphabet P) := by
        change hInhV.default = _; rfl
      rw [hdv]
      rw [cast_list_getElem?_getD (KilianCompatible.alphabet_eq (P := P) (V := V))
            e.transcript.values (Classical.choose h_ex).val default,
          cast_ne_iff]
      exact hne_pcp
  -- Apply outer-measure monotonicity, then the lifted binding bound.
  calc (experiment A pp vk ℓ rhosDist).toOuterMeasure
            {e | disagreeingAnswers (P := P) (V := V) vk e}
      ≤ (experiment A pp vk ℓ rhosDist).toOuterMeasure
            {e | VectorCommitment.check (mkVk e) (mkCm e)
                  (mkIdxs e) (mkVals e) (mkPrf e) = true ∧
                 ((mkVals e)[mkLocalIdx e]?).getD default ≠ mkValWit e} :=
        measure_mono hsub
    _ ≤ HasPositionBinding.bindingError (V := V) κ q :=
        HasPositionBinding.bindingError_lifts
          (κ := κ) (q := q)
          (experiment A pp vk ℓ rhosDist)
          mkVk mkCm mkIdxs mkVals mkPrf mkLocalIdx mkValWit

/-- **Case 2 bound.** Probability of `missingPosition` is bounded by
    `ℓ / N`, where `N` is the number of rewinding samples used by the
    reductor.

    Two narrowly-scoped hypotheses do the heavy lifting:

    * `h_queries_bound` — the PCP verifier's queries are in `[ℓ]`. This
      is a structural property of the PCP (queries can't reach past the
      proof length); concrete instances discharge it directly from
      `proofLength`.

    * `h_per_pos` — for every position `q ∈ [ℓ]`, the joint probability
      that the verifier's challenge picks `q` AND the reductor's `rhos`
      never cover `q` is at most `1/N`. This is the per-position
      content of the paper's analysis: assuming `ρ ⊥ rhos` and `rhos`
      i.i.d. `randomnessDist`, it factors as `δ_q · (1-δ_q)^N` and the
      elementary inequality `δ(1-δ)^N ≤ 1/N` (provable for any concrete
      i.i.d. `rhosDist` via Mathlib's weighted AM-GM, see proof in
      `/tmp/delta_compl_pow.lean`) closes it.

    The proof below is the *structural* union-bound argument; the per-
    position hypothesis abstracts the i.i.d. probability factorization,
    keeping the lemma model-neutral. -/
theorem bound_case2
    (A : Adversary P V spec)
    (pp : VectorCommitment.UniversalParams V)
    (vk : VectorCommitment.VerifierKey V)
    (ℓ N : ℕ)
    (rhosDist : PMF (List (PCPSystem.Randomness P)))
    (ε : ENNReal)
    (h_eps : ε = (ℓ : ENNReal) / (N : ENNReal))
    (h_queries_bound : ∀ (x : PCPSystem.Statement P)
        (ρ : PCPSystem.Randomness P),
      ∀ q ∈ PCPSystem.verifierQueries (P := P) x ρ, q < ℓ)
    (h_per_pos : ∀ q : ℕ, q < ℓ →
        (experiment A pp vk ℓ rhosDist).toOuterMeasure
          {e | q ∈ PCPSystem.verifierQueries (P := P) e.statement
                     e.transcript.randomness ∧
               q ∉ e.covered}
        ≤ (1 : ENNReal) / N) :
    (experiment A pp vk ℓ rhosDist).toOuterMeasure
        {e | missingPosition (P := P) e}
      ≤ ε := by
  -- Step 1: `missingPosition` is contained in the finite union over [ℓ].
  have hsub :
      {e : Experiment P V | missingPosition (P := P) e} ⊆
        ⋃ q ∈ Finset.range ℓ,
          {e : Experiment P V |
            q ∈ PCPSystem.verifierQueries (P := P) e.statement
                  e.transcript.randomness ∧
            q ∉ e.covered} := by
    intro e he
    obtain ⟨q, hq_in_Q, hq_notin⟩ := he
    refine Set.mem_iUnion₂.mpr ⟨q, Finset.mem_range.mpr ?_, hq_in_Q, hq_notin⟩
    exact h_queries_bound _ _ _ hq_in_Q
  -- Step 2: outer measure mono + finite union bound + per-position bound.
  calc (experiment A pp vk ℓ rhosDist).toOuterMeasure {e | missingPosition e}
      ≤ (experiment A pp vk ℓ rhosDist).toOuterMeasure
          (⋃ q ∈ Finset.range ℓ,
            {e : Experiment P V |
              q ∈ PCPSystem.verifierQueries (P := P) e.statement
                    e.transcript.randomness ∧
              q ∉ e.covered}) :=
        measure_mono hsub
    _ ≤ ∑ q ∈ Finset.range ℓ,
          (experiment A pp vk ℓ rhosDist).toOuterMeasure
            {e : Experiment P V |
              q ∈ PCPSystem.verifierQueries (P := P) e.statement
                    e.transcript.randomness ∧
              q ∉ e.covered} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _ ∈ Finset.range ℓ, (1 : ENNReal) / N := by
        apply Finset.sum_le_sum
        intro q hq
        exact h_per_pos q (Finset.mem_range.mp hq)
    _ = (ℓ : ENNReal) * ((1 : ENNReal) / N) := by
        rw [Finset.sum_const, Finset.card_range]
        simp [nsmul_eq_mul]
    _ = (ℓ : ENNReal) / N := by
        rw [mul_one_div]
    _ = ε := h_eps.symm

/-- **Containment of the bad event in the case union.**

    Every realisation in `isBad` is either in `disagreeingAnswers` or
    in `missingPosition`. Structural — no probability content.

    Proof: from `isBad`, the argument verifier accepts so the PCP
    verifier accepts on `values`; the PCP verifier rejects on
    `readAt Π̃ Q default` (same `(x, ρ)`). Hence `values ≠ readAt …`
    as lists. The well-formedness conjunct of `isBad` ensures equal
    lengths, so the lists differ at some index `i < Q.length`. At
    that index, either `Q.get i ∉ covered` (→ `missingPosition`) or
    `Q.get i ∈ covered` and the values disagree (→ `disagreeingAnswers`). -/
theorem isBad_subset_cases
    (vk : VectorCommitment.VerifierKey V) (e : Experiment P V) :
    isBad (P := P) vk e →
      disagreeingAnswers (P := P) (V := V) vk e ∨
      missingPosition (P := P) e := by
  intro h
  obtain ⟨h_len, h_pcp_rej, h_argaccept⟩ := h
  set Q := PCPSystem.verifierQueries (P := P) e.statement
              e.transcript.randomness with hQ_def
  -- Extract PCP-acceptance on `values` from `verifyTranscript = true`.
  have h_pcp_acc :
      PCPSystem.verifierDecide (P := P) e.statement e.transcript.randomness
        e.transcript.values = true := by
    have h1 : (Kilian.verifyTranscript e.statement vk e.transcript) = true :=
      h_argaccept
    simp only [Kilian.verifyTranscript, Bool.and_eq_true] at h1
    exact h1.2
  -- values ≠ readAt (same fn on equal args would give equal outputs).
  have h_ne :
      e.transcript.values ≠
        PCPSystem.readAt (P := P) e.pi_tilde Q default := by
    intro h_eq
    rw [h_eq] at h_pcp_acc
    exact Bool.true_eq_false_eq_False (h_pcp_acc.symm.trans h_pcp_rej)
  -- Length of readAt equals Q.length.
  have h_readAt_len :
      (PCPSystem.readAt (P := P) e.pi_tilde Q default).length = Q.length := by
    simp [PCPSystem.readAt]
  -- Find a differing index.
  have h_ex :
      ∃ i : ℕ, e.transcript.values[i]? ≠
        (PCPSystem.readAt (P := P) e.pi_tilde Q default)[i]? := by
    by_contra hall
    push Not at hall
    exact h_ne (List.ext_getElem? hall)
  obtain ⟨i, hi_ne⟩ := h_ex
  -- That index is < Q.length.
  have hi_lt_Q : i < Q.length := by
    by_contra hge
    push Not at hge
    have hv : e.transcript.values[i]? = none :=
      List.getElem?_eq_none (by omega)
    have hr : (PCPSystem.readAt (P := P) e.pi_tilde Q default)[i]? = none :=
      List.getElem?_eq_none (by rw [h_readAt_len]; exact hge)
    exact hi_ne (hv.trans hr.symm)
  have hi_lt_vals : i < e.transcript.values.length := by omega
  -- Case-split on whether Q.get ⟨i, hi_lt_Q⟩ ∈ covered.
  by_cases hcov : Q.get ⟨i, hi_lt_Q⟩ ∈ e.covered
  · -- Disagreement at covered position.
    refine Or.inl ⟨h_argaccept, ⟨i, hi_lt_Q⟩, hcov, ?_⟩
    -- Simplify Fin coercion and unfold the indexing.
    show e.transcript.values[i]?.getD default ≠
         (e.pi_tilde[Q.get ⟨i, hi_lt_Q⟩]?).getD default
    intro hagree
    apply hi_ne
    have h_v : e.transcript.values[i]? =
               some (e.transcript.values[i]'hi_lt_vals) :=
      List.getElem?_eq_getElem hi_lt_vals
    have h_r : (PCPSystem.readAt (P := P) e.pi_tilde Q default)[i]? =
               some ((e.pi_tilde[Q.get ⟨i, hi_lt_Q⟩]?).getD default) := by
      unfold PCPSystem.readAt
      rw [List.getElem?_map, List.getElem?_eq_getElem hi_lt_Q]
      simp [List.get_eq_getElem]
    rw [h_v, h_r]
    congr 1
    rw [h_v] at hagree
    simpa using hagree
  · -- Uncovered position → missingPosition.
    refine Or.inr ⟨Q.get ⟨i, hi_lt_Q⟩, ?_, hcov⟩
    exact List.get_mem _ _

/-- **Lemma 5.3 of [eprint 2024/1434].**

    For every adversary `A`, every aux/randomness distributions, every
    proof length `ℓ`, VC security parameter `κ`, query budget `q`, and
    slack `ε = ℓ/N`:

      Pr[bad event] ≤ ε_VC(κ, q) + ε.

    Proof: `isBad` is contained in `disagreeingAnswers ∪ missingPosition`
    (`isBad_subset_cases`), so the probability is bounded by the sum of
    each case's probability (monotone + subadditive `toOuterMeasure`),
    then bound each case by `bound_case1` and `bound_case2`. -/
theorem lemma53
    (A : Adversary P V spec)
    (pp : VectorCommitment.UniversalParams V)
    (vk : VectorCommitment.VerifierKey V)
    (ℓ N : ℕ)
    (rhosDist : PMF (List (PCPSystem.Randomness P)))
    (κ q : ℕ) (ε : ENNReal)
    (h_eps : ε = (ℓ : ENNReal) / (N : ENNReal))
    (h_queries_bound : ∀ (x : PCPSystem.Statement P)
        (ρ : PCPSystem.Randomness P),
      ∀ q ∈ PCPSystem.verifierQueries (P := P) x ρ, q < ℓ)
    (h_per_pos : ∀ q : ℕ, q < ℓ →
        (experiment A pp vk ℓ rhosDist).toOuterMeasure
          {e | q ∈ PCPSystem.verifierQueries (P := P) e.statement
                     e.transcript.randomness ∧
               q ∉ e.covered}
        ≤ (1 : ENNReal) / N) :
    (experiment A pp vk ℓ rhosDist).toOuterMeasure {e | isBad vk e}
      ≤ HasPositionBinding.bindingError (V := V) κ q + ε := by
  -- Step 1: monotonicity — the bad event is contained in the case union.
  have hsub :
      {e : Experiment P V | isBad vk e} ⊆
        {e : Experiment P V | disagreeingAnswers (P := P) (V := V) vk e} ∪
        {e : Experiment P V | missingPosition (P := P) e} := by
    intro e he
    rcases isBad_subset_cases vk e he with h | h
    · exact Or.inl h
    · exact Or.inr h
  -- Step 2: outer-measure monotone + subadditive on union.
  calc (experiment A pp vk ℓ rhosDist).toOuterMeasure {e | isBad vk e}
      ≤ (experiment A pp vk ℓ rhosDist).toOuterMeasure
          ({e | disagreeingAnswers (P := P) (V := V) vk e} ∪
           {e | missingPosition (P := P) e}) :=
        measure_mono hsub
    _ ≤ (experiment A pp vk ℓ rhosDist).toOuterMeasure
            {e | disagreeingAnswers (P := P) (V := V) vk e}
        + (experiment A pp vk ℓ rhosDist).toOuterMeasure
            {e | missingPosition (P := P) e} :=
        measure_union_le _ _
    _ ≤ HasPositionBinding.bindingError (V := V) κ q + ε := by
        exact add_le_add
          (bound_case1 A pp vk ℓ rhosDist κ q)
          (bound_case2 A pp vk ℓ N rhosDist ε h_eps
            h_queries_bound h_per_pos)

end Lemma53

end Kilian
