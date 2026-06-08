/-
Copyright (c) 2026 LeanStuff contributors. All rights reserved.
-/
import VectorCommitment.Properties.Probability.Coupling
import VectorCommitment.Properties.Probability.Instances.HidingParams
import Mathlib.Probability.Distributions.Uniform

/-!
# Salt-space high-entropy hidden-query lemma

This file formalizes the finite-query branch of the book's `lemma:cm-hiding` /
`lemma:rom-ow-high-entropy`: an adversary issuing at most `q` oracle queries
hits an *independently* sampled hidden salt `r` with probability at most
`q / |Salt| ≤ q / 2^s`.

The statement is oracle-generic — no Merkle structure — so root-hiding (H4) and
privacy (H5) instantiate it for leaf queries.  It is a *different* event from the
digest trace-collision of `Coupling.lean`: here we bound the adversary guessing a
hidden salt coordinate, not two oracle answers coinciding.

The `hidingExperiment` distribution pairs a `q`-query run with an independent
uniform hidden salt; the bad event is "some logged query decodes to the salt".
-/

namespace VectorCommitment.Probability

open scoped ENNReal

variable {spec : OracleSpec} {Salt : Type} [Fintype Salt]

/-- The hidden-query experiment: run `c` from the empty cache, then sample the
    hidden salt `r ← Salt` independently. -/
noncomputable def hiddenQueryExperiment {α : Type} [Nonempty Salt]
    (c : OracleComp spec α) :
    PMF ((α × QueryLog spec) × Salt) :=
  (c.run QueryLog.empty).bind (fun p =>
    (PMF.uniformOfFintype Salt).map (fun r => (p, r)))

/-- The bad event: some query input in the finished trace decodes to the hidden salt. -/
def hiddenQueryHit (parseSalt : spec.Domain → Option Salt) :
    Set ((α × QueryLog spec) × Salt) :=
  {x | ∃ d ∈ x.1.2.map Prod.fst, parseSalt d = some x.2}

/-- **Hidden-query bound (book `lemma:rom-ow-high-entropy`, finite-query form).**
    Sampling the hidden salt `r` independently of a `q`-query computation `c`, the
    probability that some query in `c`'s finished trace decodes to `r` is at most
    `q / |Salt|`.

    *Isolated distributional core.*  The argument is the book's union bound: by
    independence the salt is uniform given the run, so for each fixed run the hit
    probability is `(#distinct decoded salts)/|Salt| ≤ (log length)/|Salt|`, and
    the log length is `≤ q` by the query budget; averaging over runs preserves the
    bound.  Formalizing the average requires the `PMF` Fubini/`tsum` swap; it is
    kept here as the single named gap matching the book lemma. -/
theorem hidden_query_hit_le [Nonempty Salt] {α : Type}
    (parseSalt : spec.Domain → Option Salt)
    (c : OracleComp spec α) (q : Nat) (hbud : OracleComp.QueryBudget c q) :
    (hiddenQueryExperiment c).toOuterMeasure (hiddenQueryHit (α := α) parseSalt)
      ≤ (q : ENNReal) / (Fintype.card Salt) := by
  sorry

/-- **Entropy-lower-bound corollary.**  Against a salt space certified to carry
    `s` bits of entropy (`2^s ≤ |Salt|`), the hidden-query bound is `q / 2^s`. -/
theorem hidden_query_hit_le_inv_pow [Nonempty Salt] {α : Type}
    (parseSalt : spec.Domain → Option Salt)
    (c : OracleComp spec α) (q s : Nat) (hbud : OracleComp.QueryBudget c q)
    (hs : 2 ^ s ≤ Fintype.card Salt) :
    (hiddenQueryExperiment c).toOuterMeasure (hiddenQueryHit (α := α) parseSalt)
      ≤ (q : ENNReal) / 2 ^ s := by
  refine (hidden_query_hit_le parseSalt c q hbud).trans ?_
  gcongr
  exact_mod_cast hs

end VectorCommitment.Probability
