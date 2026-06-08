import Mathlib.Data.Vector.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform

/-!
# Random-oracle infrastructure for VectorCommitment

This file provides two layers:

1. **Legacy interface (L4 placeholder).** `ROFunction`, `RODistribution`,
   `ROQueryTrace` — the function-view of an RO. `RODistribution` is a
   `PMF.pure` placeholder because the full function space `List ByteArray →
   List.Vector Bool κ` has uncountable cardinality, so a uniform `PMF`
   over it cannot be honestly defined as a single distribution.

2. **Lazy-sampling model (the real RO).** `OracleSpec`, `QueryLog`,
   `OracleComp`, `query`, `simulateQ`. Operationally identical to the
   function view but well-defined: queries are sampled fresh on first
   encounter and cached. Probability of any finite event is honest.

API names mirror [VCVio](https://github.com/Verified-zkEVM/VCV-io) so that
when VCVio updates to Lean 4.28+ the dependency swap becomes a mechanical
rename (`import VectorCommitment.Properties.Probability.RandomOracle` →
`import VCVio.OracleComp.QueryTracking.CachingOracle`).
-/

-- ---------------------------------------------------------------------------
-- Layer 1: legacy interface (kept verbatim for downstream compatibility).
-- ---------------------------------------------------------------------------

/-- Idealized random oracle: a function from queries to fixed-size digests. -/
def ROFunction (κ : Nat) : Type := List ByteArray → List.Vector Bool κ

/-- The "all-zeros" random oracle. -/
def ROFunction.zero (κ : Nat) : ROFunction κ :=
  fun _ => List.Vector.replicate κ false

/-- Placeholder distribution: a Dirac mass at the all-zeros oracle. Kept
    for backwards compatibility with L4 lemma signatures. Real
    probabilistic content lives in the lazy-sampling layer below. -/
noncomputable def RODistribution (κ : Nat) : PMF (ROFunction κ) :=
  PMF.pure (ROFunction.zero κ)

/-- A query-answer trace (function-view). -/
structure ROQueryTrace (κ : Nat) where
  queries : List (List ByteArray × List.Vector Bool κ)

namespace ROQueryTrace

def empty (κ : Nat) : ROQueryTrace κ := ⟨[]⟩

instance (κ : Nat) : Inhabited (ROQueryTrace κ) := ⟨ROQueryTrace.empty κ⟩

def append {κ : Nat} (t : ROQueryTrace κ)
    (q : List ByteArray) (a : List.Vector Bool κ) : ROQueryTrace κ :=
  ⟨t.queries ++ [(q, a)]⟩

end ROQueryTrace

/-- Smoke lemma: the placeholder is a valid PMF. -/
theorem RODistribution_tsum_eq_one (κ : Nat) :
    (∑' f : ROFunction κ, RODistribution κ f) = 1 :=
  (RODistribution κ).tsum_coe

@[simp]
theorem ROQueryTrace.empty_queries (κ : Nat) :
    (ROQueryTrace.empty κ).queries = [] := rfl

@[simp]
theorem ROQueryTrace.append_queries {κ : Nat} (t : ROQueryTrace κ)
    (q : List ByteArray) (a : List.Vector Bool κ) :
    (t.append q a).queries = t.queries ++ [(q, a)] := rfl

-- ---------------------------------------------------------------------------
-- Layer 2: lazy-sampling model (the real RO).
-- ---------------------------------------------------------------------------

/-- Specification of a random oracle: query and response types, plus the
    instances needed for sampling and caching.

    For Merkle we typically instantiate with `Domain = List ByteArray`
    (tagged-input encoding handles domain separation) and
    `Range = List.Vector Bool κ` (digest). -/
structure OracleSpec where
  Domain : Type
  Range  : Type
  [decEqDomain : DecidableEq Domain]
  [fintypeRange : Fintype Range]
  [inhabitedRange : Inhabited Range]

attribute [instance] OracleSpec.decEqDomain
attribute [instance] OracleSpec.fintypeRange
attribute [instance] OracleSpec.inhabitedRange

/-- The query log: an ordered list of `(query, response)` pairs the
    oracle has produced so far. Newer entries near the head. Acts as the
    cache for lazy sampling. -/
abbrev QueryLog (spec : OracleSpec) : Type := List (spec.Domain × spec.Range)

namespace QueryLog
variable {spec : OracleSpec}

/-- The empty log. -/
def empty : QueryLog spec := ([] : List _)

instance : Inhabited (QueryLog spec) := ⟨QueryLog.empty⟩

/-- Look up a query's cached response, if any. -/
def lookup (log : QueryLog spec) (d : spec.Domain) : Option spec.Range :=
  (log.find? (fun p => p.fst = d)).map Prod.snd

/-- Append a fresh `(d, r)` pair to the log. -/
def append (log : QueryLog spec) (d : spec.Domain) (r : spec.Range) :
    QueryLog spec := (d, r) :: log

/-- Number of queries logged (with repeats; the lazy-sampler dedupes
    operationally via `lookup`). -/
def length (log : QueryLog spec) : Nat := List.length log

@[simp] theorem lookup_empty (d : spec.Domain) :
    (QueryLog.empty : QueryLog spec).lookup d = none := rfl

@[simp] theorem length_empty :
    (QueryLog.empty : QueryLog spec).length = 0 := rfl

@[simp] theorem length_append (log : QueryLog spec)
    (d : spec.Domain) (r : spec.Range) :
    (log.append d r).length = log.length + 1 := by
  simp [QueryLog.append, QueryLog.length]

end QueryLog

/-- A computation with access to the random oracle, as an operational free
    monad: either `ret` a value, or `call` the oracle on one input and
    continue with the response. Keeping the node first-order (the
    continuation ranges over `spec.Range`, a fixed type) keeps `OracleComp`
    in `Type`, so it fits the `Type`-valued adversary fields of the security
    classes, and the inductive shape exposes the structural recursion the
    trace/i.i.d. analysis runs on. -/
inductive OracleComp (spec : OracleSpec) (α : Type) : Type where
  | ret  : α → OracleComp spec α
  | call : spec.Domain → (spec.Range → OracleComp spec α) → OracleComp spec α

namespace OracleComp
variable {spec : OracleSpec}

/-- Monadic bind, by recursion on the computation tree. -/
def bind {α β} : OracleComp spec α → (α → OracleComp spec β) → OracleComp spec β
  | ret a,    f => f a
  | call d k, f => call d (fun r => (k r).bind f)

instance : Monad (OracleComp spec) where
  pure := ret
  bind := bind

/-- Query the oracle on `d`, returning its response. -/
def query (d : spec.Domain) : OracleComp spec spec.Range := call d ret

/-- Run a computation against a starting cache: on a novel query sample a
    fresh response uniformly and cache it; on a repeat reuse the cached one. -/
noncomputable def run {α} :
    OracleComp spec α → QueryLog spec → PMF (α × QueryLog spec)
  | ret a,    log => PMF.pure (a, log)
  | call d k, log =>
      match log.lookup d with
      | some r => (k r).run log
      | none =>
          (PMF.uniformOfFintype spec.Range).bind fun r =>
            (k r).run (log.append d r)

/-- Run from the empty cache; project the value distribution. -/
noncomputable def simulateQ (c : OracleComp spec α) : PMF α :=
  (c.run QueryLog.empty).map Prod.fst

/-- Run from a pre-populated cache; project the value distribution. -/
noncomputable def simulateQFrom (c : OracleComp spec α) (log : QueryLog spec) :
    PMF α :=
  (c.run log).map Prod.fst

@[simp] theorem run_ret {α} (a : α) (log : QueryLog spec) :
    (ret a : OracleComp spec α).run log = PMF.pure (a, log) := rfl

/-- `run` pushes through `bind`: the bridge from monadic experiments to their
    `PMF` semantics. Proved by induction on the computation tree. -/
@[simp] theorem run_bind {α β} (c : OracleComp spec α)
    (f : α → OracleComp spec β) (log : QueryLog spec) :
    (c.bind f).run log = (c.run log).bind (fun p => (f p.1).run p.2) := by
  induction c generalizing log with
  | ret a => simp [bind, run]
  | call d k ih =>
      simp only [bind, run]
      cases h : log.lookup d with
      | some r => simp [ih]
      | none => simp [ih, PMF.bind_bind]

end OracleComp

/-- The lazy-sampled random oracle. An alias to make the API name match
    VCVio's `randomOracle`. -/
@[inline, reducible]
def randomOracle {spec : OracleSpec} :
    spec.Domain → OracleComp spec spec.Range :=
  OracleComp.query
