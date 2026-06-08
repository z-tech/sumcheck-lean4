/-
Copyright (c) 2026 LeanStuff contributors. All rights reserved.
-/
import VectorCommitment.Src.Trait
import Mathlib.Data.ENNReal.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Hiding — the ROM security obligation and its honest floor

This file declares the goal-shaped `HasROMHiding`: a finite-query random-oracle
hiding obligation stated against **fixed** real/ideal games and a **fixed** error
expression. An instance supplies only the games, the error, and the bound
*proof* — it cannot redefine what hiding means. (It replaces the former generic
`HasHiding`, whose ROM instance measured a *collision* advantage that does not
capture hiding.)

The deep `etvDist real ideal ≤ error` reduction (the book's simulator-based
proof: basic-commitment hiding → bottom-up Merkle root-hiding hybrid →
selective-opening privacy) is a multi-stage formalization. Until the
oracle-native commitment game lands, **no** `HasROMHiding` instance is installed
for the Merkle scheme — hiding is reported OPEN rather than discharged by a
fixed-oracle (false) or `real = ideal` (vacuous) instance. See
`VectorCommitment/ROADMAP.md`.

The honest floor this file proves:

* `PMF.etvDist` total-variation distance and `etvDist_self`;
* `PerfectHiding`, the distributional (perfect) hiding predicate, and a
  `not_perfectHiding_singleton` negative result demonstrating the predicate is
  non-vacuous (a scheme injective under a fixed salt is *not* hiding).

The salt-size arithmetic certificates (`2 ^ s ≤ |Salt|`) live in
`VectorCommitment/Properties/Probability/Instances/HidingParams.lean` and the
`*_salt_card_ge_lam` capstones.
-/

namespace PMF

variable {α : Type*}

/-- Total-variation distance between two `PMF`s, in the one-sided event-sup form
    `⨆ E, μ(E) − ν(E)` (truncated `ENNReal` subtraction). For `PMF`s this equals
    the usual `½ ∑ₐ |μ a − ν a|`; the event form is the shape the ROM
    indistinguishability bounds are stated in. -/
noncomputable def etvDist (μ ν : PMF α) : ENNReal :=
  ⨆ E : Set α, μ.toOuterMeasure E - ν.toOuterMeasure E

/-- A distribution has zero total-variation distance from itself. -/
@[simp] theorem etvDist_self (μ : PMF α) : μ.etvDist μ = 0 := by
  simp only [etvDist, tsub_self, iSup_const]

end PMF

/-! ## Distributional (perfect) hiding — the non-vacuity floor -/

/-- **Perfect (distributional) hiding.** Under a salt distribution `saltDist`,
    the commitment to any two values is identically distributed.

    This is *not* computational hiding — there is no adversary, no security
    parameter, no negligible advantage; it compares the raw mapped
    distributions. It is the information-theoretic floor that the ROM
    `HasROMHiding` obligation strengthens to a finite-query, bounded-advantage
    statement. -/
def PerfectHiding {Value Salt Com : Type} (saltDist : PMF Salt)
    (commit : Value → Salt → Com) : Prop :=
  ∀ v₀ v₁ : Value, saltDist.map (commit v₀) = saltDist.map (commit v₁)

/-- **Singleton-salt negative result.** With a single (deterministic) salt `s₀`,
    a scheme whose commitment separates two values under `s₀` does *not* satisfy
    `PerfectHiding`. This witnesses that `PerfectHiding` is non-vacuous: it is a
    real constraint that injective-under-a-fixed-salt schemes fail. -/
theorem not_perfectHiding_singleton {Value Salt Com : Type}
    (s₀ : Salt) (commit : Value → Salt → Com) (v₀ v₁ : Value)
    (hsep : commit v₀ s₀ ≠ commit v₁ s₀) :
    ¬ PerfectHiding (PMF.pure s₀) commit := by
  intro h
  have hmap := h v₀ v₁
  rw [PMF.map_pure, PMF.map_pure] at hmap
  have hsupp := congrArg PMF.support hmap
  rw [PMF.support_pure, PMF.support_pure] at hsupp
  -- hsupp : {commit v₀ s₀} = {commit v₁ s₀}
  have hmem : commit v₀ s₀ ∈ ({commit v₁ s₀} : Set Com) := by
    rw [← hsupp]; exact Set.mem_singleton _
  exact hsep (Set.mem_singleton_iff.mp hmem)

/-- Concrete instance of the singleton-salt counterexample: the identity
    commitment `commit v _ = v` over `Bool` separates `false` and `true`, so it
    is not perfectly hiding under any single salt. -/
theorem not_perfectHiding_identity_bool (s₀ : Unit) :
    ¬ PerfectHiding (PMF.pure s₀) (fun (v : Bool) (_ : Unit) => v) := by
  refine not_perfectHiding_singleton s₀ _ false true ?_
  decide

/-! ## The ROM hiding obligation -/

/-- **Finite-query ROM hiding obligation.** Stated against fixed real and ideal
    games (`PMF`s over a hidden digest type) and a fixed error expression; an
    instance supplies the games, the error, and the bound proof but cannot
    redefine the notion. The single security guarantee is that the real and
    ideal games are `error`-close in total-variation distance.

    No instance is installed for the Merkle scheme yet: the honest real game is
    the oracle-native commitment distribution, whose construction and bound are
    the remaining work (see `ROADMAP.md`). Installing a fixed-oracle or
    real = ideal placeholder would be false or vacuous, so hiding is reported
    OPEN until the real proof lands. -/
class HasROMHiding (V : Type) [VectorCommitment V] where
  /-- The hidden target type the games range over (e.g. the commitment root
      digest). -/
  Hidden : Type
  /-- The real root-hiding game: the honest commitment-root distribution. -/
  rootRealGame : PMF Hidden
  /-- The ideal game: a uniform hidden digest. -/
  rootIdealGame : PMF Hidden
  /-- The fixed root-hiding error, `n·q / |Salt| + (n−1)·q / |Digest|²`. -/
  rootError : ENNReal
  /-- The fixed selective-opening privacy error,
      `Q·n·q / |Salt| + Q·n·q / |Digest|²` (loose public bound). -/
  privacyError : ENNReal
  /-- The central guarantee: real and ideal root games are `rootError`-close. -/
  root_hiding : rootRealGame.etvDist rootIdealGame ≤ rootError
