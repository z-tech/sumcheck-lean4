/-
Copyright (c) 2026 LeanStuff contributors. All rights reserved.
-/
import VectorCommitment.Properties.Probability.CheckOracle
import VectorCommitment.Properties.Probability.Coupling

/-!
# Structural reduction: a winning break forces a trace collision

The shared core behind `binding_win_le_trace_collision` and
`extraction_win_le_trace_collision`. Two facts about `OracleComp.run`:

* **`run_nodup`** — lazy sampling appends a `(d, r)` entry only on a cache
  *miss* (`lookup d = none`), so a finished log never lists the same query
  input twice: `(log.map Prod.fst).Nodup`. The realized oracle is therefore a
  genuine partial function.

* **`run_mem_log`** — every value a `query d` returns on the run path is the
  one recorded for `d` in the finished log (`log.lookup d = some r`).

Together with a functional log these turn "two accepting authentication paths
to one root from distinct leaves" into an explicit colliding pair.
-/

namespace VectorCommitment.Probability

open OracleComp ROHasher

variable {spec : OracleSpec}

/-- `run_bind` phrased for the `>>=` notation produced by do-blocks. -/
theorem run_bind' {α β} (c : OracleComp spec α) (f : α → OracleComp spec β)
    (log : QueryLog spec) :
    (c >>= f).run log = (c.run log).bind (fun p => (f p.1).run p.2) :=
  OracleComp.run_bind c f log

/-- `run` of `pure` (the do-block return). -/
@[simp] theorem run_pure {α} (a : α) (log : QueryLog spec) :
    (pure a : OracleComp spec α).run log = PMF.pure (a, log) := rfl

-- ---------------------------------------------------------------------------
-- Encoding injectivity and no-collision ⇒ output-determines-input.
-- ---------------------------------------------------------------------------

/-- The internal-node encoding is injective in the child list. -/
theorem encodeNodes_inj {κ : Nat} {c0 c1 : List (List.Vector Bool κ)}
    (h : encodeNodes c0 = encodeNodes c1) : c0 = c1 := by
  unfold encodeNodes at h
  simp only [List.cons.injEq, true_and] at h
  exact List.map_injective_iff.mpr vecBytes_injective h

/-- A cached lookup witnesses a log entry. -/
theorem mem_of_lookup {κ : Nat} {log : QueryLog (MerkleROSpec κ)}
    {d : (MerkleROSpec κ).Domain} {r : (MerkleROSpec κ).Range}
    (h : log.lookup d = some r) : (d, r) ∈ log := by
  unfold QueryLog.lookup at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨e, hfind, hr⟩ := h
  have hmem := List.mem_of_find?_eq_some hfind
  have hd : e.1 = d := by have := List.find?_some hfind; simpa using this
  obtain ⟨e1, e2⟩ := e
  simp only at hd hr; subst hd; subst hr; exact hmem

/-- Under a collision-free log, equal outputs force equal inputs. -/
theorem lookup_inj_of_no_collision {κ : Nat} {log : QueryLog (MerkleROSpec κ)}
    (hnc : ¬ QueryLog.hasCollision log)
    {d1 d2 : (MerkleROSpec κ).Domain} {r : (MerkleROSpec κ).Range}
    (h1 : log.lookup d1 = some r) (h2 : log.lookup d2 = some r) : d1 = d2 := by
  by_contra hne
  exact hnc ⟨(d1, r), mem_of_lookup h1, (d2, r), mem_of_lookup h2, hne, rfl⟩

-- ---------------------------------------------------------------------------
-- Pure reconstruction-via-log and its injective descent.
-- ---------------------------------------------------------------------------

/-- Walk the copath using the finished log as the (partial) oracle: at each
    level look up the parent digest for the current children; `none` if absent.
    Mirrors `ROHasher.walkCopathOracle` post-hoc on the log. -/
def walkViaLog {κ : Nat} (log : QueryLog (MerkleROSpec κ)) :
    Nat → List.Vector Bool κ → List (List.Vector Bool κ) →
      Option (List.Vector Bool κ)
  | _,   acc, []          => some acc
  | pos, acc, sib :: rest =>
      match log.lookup (encodeNodes (if pos % 2 = 1 then [acc, sib] else [sib, acc])) with
      | some parent => walkViaLog log ((pos - 1) / 2) parent rest
      | none        => none

/-- **No-collision descent.** Under a collision-free log, two `walkViaLog` runs
    that reach the same digest `r` from the same position (with equal-length
    copaths) must have started from the same accumulator. Contrapositive of the
    binding cascade: distinct leaves to one root ⇒ a collision. -/
theorem walkViaLog_inj {κ : Nat} {log : QueryLog (MerkleROSpec κ)}
    (hnc : ¬ QueryLog.hasCollision log) :
    ∀ (cp0 cp1 : List (List.Vector Bool κ)) (pos : Nat)
      (acc0 acc1 r : List.Vector Bool κ),
      cp0.length = cp1.length →
      walkViaLog log pos acc0 cp0 = some r →
      walkViaLog log pos acc1 cp1 = some r →
      acc0 = acc1 := by
  intro cp0
  induction cp0 with
  | nil =>
      intro cp1 pos acc0 acc1 r hlen h0 h1
      have hc1 : cp1 = [] := List.length_eq_zero_iff.mp hlen.symm
      subst hc1
      simp only [walkViaLog, Option.some.injEq] at h0 h1
      rw [h0, h1]
  | cons sib0 rest0 ih =>
      intro cp1 pos acc0 acc1 r hlen h0 h1
      cases cp1 with
      | nil => simp at hlen
      | cons sib1 rest1 =>
          simp only [walkViaLog] at h0 h1
          cases hlk0 : log.lookup (encodeNodes
              (if pos % 2 = 1 then [acc0, sib0] else [sib0, acc0])) with
          | none => rw [hlk0] at h0; simp at h0
          | some parent0 =>
              cases hlk1 : log.lookup (encodeNodes
                  (if pos % 2 = 1 then [acc1, sib1] else [sib1, acc1])) with
              | none => rw [hlk1] at h1; simp at h1
              | some parent1 =>
                  rw [hlk0] at h0; rw [hlk1] at h1
                  have hlen' : rest0.length = rest1.length := by simpa using hlen
                  have hpar : parent0 = parent1 :=
                    ih rest1 ((pos - 1) / 2) parent0 parent1 r hlen' h0 h1
                  subst hpar
                  have hdeq := encodeNodes_inj (lookup_inj_of_no_collision hnc hlk0 hlk1)
                  by_cases hp : pos % 2 = 1
                  · simp only [hp, if_true, List.cons.injEq] at hdeq; exact hdeq.1
                  · simp only [hp, if_false, List.cons.injEq] at hdeq; exact hdeq.2.1

/-- Lazy sampling never re-lists a query input: the finished log's inputs are
    `Nodup`, starting from any `Nodup` log. -/
theorem run_nodup {α} (c : OracleComp spec α) :
    ∀ (log : QueryLog spec) p, p ∈ (c.run log).support →
      (log.map Prod.fst).Nodup → (p.2.map Prod.fst).Nodup := by
  induction c with
  | ret a =>
      intro log p hp hnd
      simp only [OracleComp.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hp
      subst hp; exact hnd
  | call d k ih =>
      intro log p hp hnd
      rw [OracleComp.run] at hp
      cases hlk : log.lookup d with
      | some r => rw [hlk] at hp; exact ih r log p hp hnd
      | none =>
          rw [hlk] at hp
          simp only [PMF.support_bind, Set.mem_iUnion] at hp
          obtain ⟨r, _, hpr⟩ := hp
          refine ih r (log.append d r) p hpr ?_
          rw [QueryLog.append, List.map_cons, List.nodup_cons]
          refine ⟨?_, hnd⟩
          intro hmem
          obtain ⟨e, he, hee⟩ := List.mem_map.mp hmem
          exact (forall_ne_of_lookup_none hlk e he) hee

/-- In a functional (input-`Nodup`) log, a membership uniquely fixes the lookup. -/
theorem lookup_eq_of_mem_nodup {κ : Nat} {log : QueryLog (MerkleROSpec κ)}
    {d : (MerkleROSpec κ).Domain} {r : (MerkleROSpec κ).Range}
    (hmem : (d, r) ∈ log) (hnd : (log.map Prod.fst).Nodup) :
    log.lookup d = some r := by
  induction log with
  | nil => simp at hmem
  | cons e rest ih =>
      rw [List.map_cons, List.nodup_cons] at hnd
      obtain ⟨hnotin, hndrest⟩ := hnd
      rw [List.mem_cons] at hmem
      show ((e :: rest).find? (fun p => p.fst = d)).map Prod.snd = some r
      rw [List.find?_cons]
      by_cases he : e.fst = d
      · rcases hmem with rfl | hmem
        · simp
        · exact absurd (he ▸ List.mem_map.mpr ⟨(d, r), hmem, rfl⟩) hnotin
      · rcases hmem with rfl | hmem
        · exact absurd rfl he
        · simp only [he, decide_false]
          exact ih hmem hndrest

/-- `run` only extends the cache, so the starting log is a suffix of every
    finished log. -/
theorem run_suffix {α} (c : OracleComp spec α) :
    ∀ (log : QueryLog spec) p, p ∈ (c.run log).support → log <:+ p.2 := by
  induction c with
  | ret a =>
      intro log p hp
      simp only [OracleComp.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hp
      subst hp; exact List.suffix_refl _
  | call d k ih =>
      intro log p hp
      rw [OracleComp.run] at hp
      cases hlk : log.lookup d with
      | some r => rw [hlk] at hp; exact ih r log p hp
      | none =>
          rw [hlk] at hp
          simp only [PMF.support_bind, Set.mem_iUnion] at hp
          obtain ⟨r, _, hpr⟩ := hp
          exact (List.suffix_cons _ _).trans (ih r (log.append d r) p hpr)

/-- A single `query d` records `(d, response)` in its finished log. -/
theorem query_mem_log {κ : Nat} {d : (MerkleROSpec κ).Domain}
    {r : (MerkleROSpec κ).Range} {log0 logf : QueryLog (MerkleROSpec κ)}
    (h : (r, logf) ∈ ((OracleComp.query d).run log0).support) : (d, r) ∈ logf := by
  unfold OracleComp.query at h
  rw [OracleComp.run] at h
  cases hlk : log0.lookup d with
  | some r' =>
      rw [hlk] at h
      simp only [OracleComp.run_ret, PMF.support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at h
      obtain ⟨hr, hlog⟩ := h
      subst hr; subst hlog; exact mem_of_lookup hlk
  | none =>
      rw [hlk] at h
      simp only [OracleComp.run_ret, PMF.support_bind, Set.mem_iUnion,
        PMF.support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
      obtain ⟨x, _, hr, hlog⟩ := h
      subst hr; subst hlog
      rw [QueryLog.append]; exact List.mem_cons_self ..

/-- Support-restricted monotonicity of the PMF outer measure: it suffices that
    `s` and `t` agree on the support. -/
theorem toOuterMeasure_mono_support {α} (p : PMF α) {s t : Set α}
    (h : ∀ x ∈ p.support, x ∈ s → x ∈ t) :
    p.toOuterMeasure s ≤ p.toOuterMeasure t := by
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
  refine ENNReal.tsum_le_tsum (fun x => ?_)
  by_cases hs : x ∈ s
  · by_cases hp0 : p x = 0
    · simp [hs, hp0]
    · have ht : x ∈ t := h x ((p.mem_support_iff x).mpr hp0) hs
      simp [hs, ht]
  · simp [hs]

-- ---------------------------------------------------------------------------
-- The monadic bridge: a finished `reconstructRootOracle`/`checkOracle` run is
-- reproduced by the pure `walkViaLog` on its final log.
-- ---------------------------------------------------------------------------

/-- A finished `walkCopathOracle` run is reproduced by `walkViaLog` on its final
    log (which is functional by `run_nodup`). -/
theorem walkCopathOracle_run {κ : Nat} :
    ∀ (cp : List (List.Vector Bool κ)) (pos : Nat) (acc d : List.Vector Bool κ)
      (log0 logf : QueryLog (MerkleROSpec κ)),
      (log0.map Prod.fst).Nodup →
      (d, logf) ∈ ((walkCopathOracle pos acc cp).run log0).support →
      walkViaLog logf pos acc cp = some d := by
  intro cp
  induction cp with
  | nil =>
      intro pos acc d log0 logf _ hsup
      have he : walkCopathOracle pos acc ([] : List (List.Vector Bool κ))
          = OracleComp.ret acc := rfl
      rw [he, OracleComp.run_ret] at hsup
      simp only [PMF.support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hsup
      obtain ⟨hd, hlog⟩ := hsup
      subst hd; subst hlog; rfl
  | cons sib rest ih =>
      intro pos acc d log0 logf hnd hsup
      rw [walkCopathOracle, run_bind'] at hsup
      simp only [PMF.support_bind, Set.mem_iUnion] at hsup
      obtain ⟨⟨parent, log1⟩, hq, hrec⟩ := hsup
      have hmem1 : (encodeNodes (if pos % 2 = 1 then [acc, sib] else [sib, acc]), parent) ∈ log1 :=
        query_mem_log hq
      have hnd1 : (log1.map Prod.fst).Nodup := run_nodup _ log0 (parent, log1) hq hnd
      have hsuf : log1 <:+ logf := run_suffix _ log1 (d, logf) hrec
      have hmemf : (encodeNodes (if pos % 2 = 1 then [acc, sib] else [sib, acc]), parent) ∈ logf :=
        hsuf.mem hmem1
      have hndf : (logf.map Prod.fst).Nodup := run_nodup _ log1 (d, logf) hrec hnd1
      have hlook : logf.lookup (encodeNodes (if pos % 2 = 1 then [acc, sib] else [sib, acc]))
          = some parent := lookup_eq_of_mem_nodup hmemf hndf
      have hwrec : walkViaLog logf ((pos - 1) / 2) parent rest = some d :=
        ih ((pos - 1) / 2) parent d log1 logf hnd1 hrec
      rw [walkViaLog, hlook]; exact hwrec

/-- A finished `reconstructRootOracle` run is reproduced by `walkViaLog` from the
    leaf digest, with the leaf query recorded in the final log. -/
theorem reconstructRootOracle_run {κ : Nat} {n i : Nat}
    {value salt : List.Vector Bool κ} {cp : List (List.Vector Bool κ)}
    {log0 logf : QueryLog (MerkleROSpec κ)} {d : List.Vector Bool κ}
    (hnd : (log0.map Prod.fst).Nodup)
    (hsup : (d, logf) ∈ ((reconstructRootOracle n i value salt cp).run log0).support) :
    ∃ leaf : List.Vector Bool κ,
      (encodeLeaf value salt, leaf) ∈ logf ∧
      walkViaLog logf (n - 1 + i) leaf cp = some d := by
  rw [reconstructRootOracle, run_bind'] at hsup
  simp only [PMF.support_bind, Set.mem_iUnion] at hsup
  obtain ⟨⟨leaf, log1⟩, hq, hrec⟩ := hsup
  refine ⟨leaf, ?_, ?_⟩
  · exact (run_suffix _ log1 (d, logf) hrec).mem (query_mem_log hq)
  · exact walkCopathOracle_run cp (n - 1 + i) leaf d log1 logf
      (run_nodup _ log0 (leaf, log1) hq hnd) hrec

/-- A singleton `checkOracle` that accepts pins the opening proof to one entry
    `(salt, copath)` of depth `⌊log₂ n⌋` whose `reconstructRootOracle` produced
    exactly `root`. -/
theorem checkOracle_singleton_accept {κ : Nat} {n i : Nat}
    {root v : List.Vector Bool κ} {pf : OpeningProof (ROHasher.ROHasherValue κ)}
    {log0 logf : QueryLog (MerkleROSpec κ)}
    (h : (true, logf) ∈ ((checkOracle n root
            { indices := [i], values := [v] } pf).run log0).support) :
    ∃ s cp, pf.entries = [(s, cp)] ∧ cp.length = PerfectBinary.log2Floor n ∧
      (root, logf) ∈ ((reconstructRootOracle n i v s cp).run log0).support := by
  unfold checkOracle at h
  split at h
  · -- length guard tripped ⇒ the run is `pure false`, contradicting the `true` outcome
    simp only [run_pure, PMF.support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
    exact absurd h.1 (by decide)
  · -- guard passed ⇒ the proof has exactly one entry
    rename_i hcond
    simp only [List.length_singleton, ne_eq, not_or, not_not] at hcond
    obtain ⟨e, he⟩ := List.length_eq_one_iff.mp hcond.2.symm
    rw [he] at h
    simp only [List.zip_cons_cons, List.zip_nil_right, List.foldlM_cons, List.foldlM_nil,
      Bool.true_and] at h
    rw [run_bind'] at h
    simp only [PMF.support_bind, Set.mem_iUnion] at h
    obtain ⟨⟨b', log1⟩, h1, h2⟩ := h
    simp only [run_pure, PMF.support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2
    obtain ⟨hb, hl⟩ := h2; subst hb; subst hl
    rw [run_bind'] at h1
    simp only [PMF.support_bind, Set.mem_iUnion] at h1
    obtain ⟨⟨r, log2⟩, hr, hres⟩ := h1
    simp only [run_pure, PMF.support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hres
    obtain ⟨hval, hl2⟩ := hres
    rw [eq_comm, Bool.and_eq_true] at hval
    obtain ⟨hroot, hlen⟩ := hval
    subst hl2
    exact ⟨e.1, e.2, he, of_decide_eq_true hlen, of_decide_eq_true hroot ▸ hr⟩

/-- `walkViaLog` is monotone under (functional) log extension: a reconstruction
    that succeeds on a suffix still succeeds on the whole log. -/
theorem walkViaLog_mono {κ : Nat} {log1 logf : QueryLog (MerkleROSpec κ)}
    (hsuf : log1 <:+ logf) (hndf : (logf.map Prod.fst).Nodup) :
    ∀ (cp : List (List.Vector Bool κ)) (pos : Nat) (acc r : List.Vector Bool κ),
      walkViaLog log1 pos acc cp = some r → walkViaLog logf pos acc cp = some r := by
  intro cp
  induction cp with
  | nil => intro pos acc r h; simpa [walkViaLog] using h
  | cons sib rest ih =>
      intro pos acc r h
      rw [walkViaLog] at h ⊢
      cases hlk1 : log1.lookup (encodeNodes (if pos % 2 = 1 then [acc, sib] else [sib, acc])) with
      | none => rw [hlk1] at h; simp at h
      | some parent =>
          rw [hlk1] at h
          rw [lookup_eq_of_mem_nodup (hsuf.mem (mem_of_lookup hlk1)) hndf]
          exact ih ((pos - 1) / 2) parent r h

/-- **Core uniqueness lemma.** Under a collision-free trace, two accepted
    openings of the same `root` at the same index `i` (equal-depth copaths) must
    reveal the same value. Both ROM bounds derive a collision from its
    contrapositive. -/
theorem accepted_value_unique {κ : Nat} {n i : Nat}
    {root v0 v1 s0 s1 : List.Vector Bool κ} {cp0 cp1 : List (List.Vector Bool κ)}
    {log0 log1 logf : QueryLog (MerkleROSpec κ)}
    (hnd : (log0.map Prod.fst).Nodup)
    (hlen : cp0.length = cp1.length)
    (hnc : ¬ QueryLog.hasCollision logf)
    (h0 : (root, log1) ∈ ((reconstructRootOracle n i v0 s0 cp0).run log0).support)
    (h1 : (root, logf) ∈ ((reconstructRootOracle n i v1 s1 cp1).run log1).support) :
    v0 = v1 := by
  have hnd1 : (log1.map Prod.fst).Nodup := run_nodup _ log0 (root, log1) h0 hnd
  have hndf : (logf.map Prod.fst).Nodup := run_nodup _ log1 (root, logf) h1 hnd1
  obtain ⟨leaf0, hmem0, hwalk0⟩ := reconstructRootOracle_run hnd h0
  obtain ⟨leaf1, hmem1, hwalk1⟩ := reconstructRootOracle_run hnd1 h1
  have hsuf : log1 <:+ logf := run_suffix _ log1 (root, logf) h1
  have hwalk0f : walkViaLog logf (n - 1 + i) leaf0 cp0 = some root :=
    walkViaLog_mono hsuf hndf cp0 (n - 1 + i) leaf0 root hwalk0
  have hleaf : leaf0 = leaf1 :=
    walkViaLog_inj hnc cp0 cp1 (n - 1 + i) leaf0 leaf1 root hlen hwalk0f hwalk1
  have hmem0f : (encodeLeaf v0 s0, leaf1) ∈ logf := hleaf ▸ hsuf.mem hmem0
  have heq : encodeLeaf v0 s0 = encodeLeaf v1 s1 :=
    lookup_inj_of_no_collision hnc
      (lookup_eq_of_mem_nodup hmem0f hndf) (lookup_eq_of_mem_nodup hmem1 hndf)
  exact (encodeLeaf_inj heq).1

end VectorCommitment.Probability
