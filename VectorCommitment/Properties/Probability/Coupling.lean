/-
Copyright (c) 2026 LeanStuff contributors. All rights reserved.
-/
import VectorCommitment.Properties.Probability.RandomOracle
import VectorCommitment.Properties.Probability.ROHasher
import VectorCommitment.Properties.Probability.Collision
import Mathlib.Data.Fintype.Vector

/-!
# Trace collision bound for the lazy-sampling oracle

The probability that a finished query trace contains two distinct queries with
the same response is at most `collisionBound κ q = q(q-1)/2^(κ+1)`, for a
computation spending at most `q` oracle queries.

The proof is a direct induction on the computation. Each fresh oracle query
draws a uniform response; it collides with one of the `≤ m` responses already
cached with probability `≤ m/|R|`. Accumulated over the `≤ q` fresh queries
this telescopes to `(0 + 1 + ⋯ + (q-1))/|R| = q(q-1)/(2|R|)`, the birthday
bound — no separate eager sampling space is needed.
-/

namespace VectorCommitment.Probability

open OracleComp
open scoped ENNReal

/-- A finished query log *collides* when it holds two entries with distinct
    query inputs but identical oracle responses — the "random oracle repeated a
    digest" bad event the binding / extractability reductions branch on. -/
def QueryLog.hasCollision {spec : OracleSpec} (log : QueryLog spec) : Prop :=
  ∃ e₁ ∈ log, ∃ e₂ ∈ log, e₁.1 ≠ e₂.1 ∧ e₁.2 = e₂.2

/-- A computation *spends at most `q` queries* when every finished run from the
    empty cache leaves a log of length `≤ q`. Lazy sampling appends only on a
    cache miss, so `log.length` counts the distinct queries actually issued. -/
def OracleComp.QueryBudget {spec : OracleSpec} {α : Type}
    (c : OracleComp spec α) (q : Nat) : Prop :=
  ∀ p ∈ (c.run QueryLog.empty).support, p.2.length ≤ q

variable {spec : OracleSpec}

/-- `run` only ever extends the cache, so every reachable final log is at least
    as long as the starting one. -/
theorem run_length_le {α} (c : OracleComp spec α) :
    ∀ (log : QueryLog spec) p, p ∈ (c.run log).support → log.length ≤ p.2.length := by
  induction c with
  | ret a =>
      intro log p hp
      simp only [run_ret, PMF.support_pure, Set.mem_singleton_iff] at hp
      subst hp; exact le_rfl
  | call d k ih =>
      intro log p hp
      rw [run] at hp
      cases hlk : log.lookup d with
      | some r => rw [hlk] at hp; exact ih r log p hp
      | none =>
          rw [hlk] at hp
          simp only [PMF.support_bind, Set.mem_iUnion] at hp
          obtain ⟨r, _, hpr⟩ := hp
          have := ih r (log.append d r) p hpr
          simp only [QueryLog.length_append] at this
          omega

/-- `log.lookup d = none` means no entry has domain input `d`. -/
theorem forall_ne_of_lookup_none {log : QueryLog spec} {d : spec.Domain}
    (h : log.lookup d = none) : ∀ e ∈ log, e.1 ≠ d := by
  intro e he
  rw [QueryLog.lookup, Option.map_eq_none_iff, List.find?_eq_none] at h
  have := h e he
  simpa using this

/-- Appending a fresh-domain entry `(d, r)` to a collision-free log creates a
    collision exactly when `r` already appears as some cached response. -/
theorem hasCollision_append_iff {log : QueryLog spec} {d : spec.Domain}
    {r : spec.Range} (hd : log.lookup d = none) (hlog : ¬ QueryLog.hasCollision log) :
    QueryLog.hasCollision (log.append d r) ↔ r ∈ log.map Prod.snd := by
  have hfresh := forall_ne_of_lookup_none hd
  constructor
  · rintro ⟨e₁, he₁, e₂, he₂, hne, heq⟩
    simp only [QueryLog.append, List.mem_cons] at he₁ he₂
    rcases he₁ with rfl | he₁ <;> rcases he₂ with rfl | he₂
    · exact absurd rfl hne
    · exact List.mem_map.mpr ⟨e₂, he₂, heq.symm⟩
    · exact List.mem_map.mpr ⟨e₁, he₁, heq⟩
    · exact absurd ⟨e₁, he₁, e₂, he₂, hne, heq⟩ hlog
  · intro hr
    obtain ⟨e, he, hee⟩ := List.mem_map.mp hr
    exact ⟨(d, r), by simp [QueryLog.append], e, by simp [QueryLog.append, he],
      (hfresh e he).symm, hee.symm⟩

/-- **Trace collision bound, inductive core.** For a computation run from a
    collision-free cache of length `m`, every reachable final log having length
    `≤ q`, the probability the final log collides is at most
    `(∑ i ∈ Ico m q, i)/|R|`. At `m = 0` the sum is `q(q-1)/2`. -/
theorem run_coll_le {α} (q : Nat) (c : OracleComp spec α) :
    ∀ (log : QueryLog spec), ¬ QueryLog.hasCollision log →
      (∀ p ∈ (c.run log).support, p.2.length ≤ q) →
      (c.run log).toOuterMeasure {p | QueryLog.hasCollision p.2}
        ≤ (∑ i ∈ Finset.Ico log.length q, (i : ℝ≥0∞)) / (Fintype.card spec.Range) := by
  induction c with
  | ret a =>
      intro log hlog _
      simp only [run_ret, PMF.toOuterMeasure_pure_apply, Set.mem_setOf_eq]
      rw [if_neg hlog]; exact zero_le _
  | call d k ih =>
      intro log hlog hbud
      cases hlk : log.lookup d with
      | some r =>
          have hrun : (call d k).run log = (k r).run log := by rw [run, hlk]
          rw [hrun] at hbud ⊢
          exact ih r log hlog hbud
      | none =>
          have hrun : (call d k).run log
              = (PMF.uniformOfFintype spec.Range).bind
                  (fun r => (k r).run (log.append d r)) := by rw [run, hlk]
          rw [hrun] at hbud ⊢
          classical
          set N : ℝ≥0∞ := (Fintype.card spec.Range : ℝ≥0∞) with hN
          have hcard : N ≠ 0 := by rw [hN]; simp [Fintype.card_ne_zero]
          have hcardtop : N ≠ ⊤ := by rw [hN]; exact ENNReal.natCast_ne_top _
          -- m < q, from a reachable length-(m+1) outcome.
          have hmlt : log.length < q := by
            obtain ⟨r₀⟩ := (inferInstance : Nonempty spec.Range)
            obtain ⟨p₀, hp₀⟩ := ((k r₀).run (log.append d r₀)).support_nonempty
            have hmem : p₀ ∈ ((PMF.uniformOfFintype spec.Range).bind
                (fun r => (k r).run (log.append d r))).support := by
              rw [PMF.support_bind]
              exact Set.mem_iUnion₂.mpr ⟨r₀, by simp [PMF.support_uniformOfFintype], hp₀⟩
            have h1 := hbud p₀ hmem
            have h2 := run_length_le (k r₀) (log.append d r₀) p₀ hp₀
            simp only [QueryLog.length_append] at h2
            omega
          set B : Finset spec.Range := (log.map Prod.snd).toFinset with hB
          have hBcard : (B.card : ℝ≥0∞) ≤ (log.length : ℝ≥0∞) := by
            have : B.card ≤ log.length := by
              calc B.card ≤ (log.map Prod.snd).length := List.toFinset_card_le _
                _ = log.length := by simp [QueryLog.length]
            exact_mod_cast this
          set C : ℝ≥0∞ := (∑ i ∈ Finset.Ico (log.length + 1) q, (i : ℝ≥0∞)) / N with hC
          -- Termwise majorant of the per-response collision probability.
          have hterm : ∀ r, ((k r).run (log.append d r)).toOuterMeasure
              {p | QueryLog.hasCollision p.2}
              ≤ (if r ∈ B then (1 : ℝ≥0∞) else 0) + C := by
            intro r
            by_cases hr : r ∈ B
            · rw [if_pos hr]
              calc ((k r).run (log.append d r)).toOuterMeasure {p | QueryLog.hasCollision p.2}
                  ≤ ((k r).run (log.append d r)).toOuterMeasure Set.univ :=
                    ((k r).run (log.append d r)).toOuterMeasure_mono (Set.subset_univ _)
                _ = 1 := (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (Set.subset_univ _)
                _ ≤ 1 + C := le_add_right le_rfl
            · rw [if_neg hr, zero_add]
              have hr' : r ∉ log.map Prod.snd := by simpa [hB, List.mem_toFinset] using hr
              have hnc : ¬ QueryLog.hasCollision (log.append d r) := by
                rw [hasCollision_append_iff hlk hlog]; exact hr'
              have hbud' : ∀ p ∈ ((k r).run (log.append d r)).support, p.2.length ≤ q := by
                intro p hp
                refine hbud p ?_
                rw [PMF.support_bind]
                exact Set.mem_iUnion₂.mpr ⟨r, by simp [PMF.support_uniformOfFintype], hp⟩
              have := ih r (log.append d r) hnc hbud'
              simpa only [QueryLog.length_append, hC] using this
          -- Sum the majorant.
          rw [PMF.toOuterMeasure_bind_apply]
          have hsum : ∑' r, (PMF.uniformOfFintype spec.Range) r
                * ((k r).run (log.append d r)).toOuterMeasure {p | QueryLog.hasCollision p.2}
              ≤ (log.length : ℝ≥0∞) / N + C := by
            calc ∑' r, (PMF.uniformOfFintype spec.Range) r
                    * ((k r).run (log.append d r)).toOuterMeasure {p | QueryLog.hasCollision p.2}
                ≤ ∑' r, (PMF.uniformOfFintype spec.Range) r
                    * ((if r ∈ B then (1 : ℝ≥0∞) else 0) + C) :=
                  ENNReal.tsum_le_tsum (fun r => by gcongr; exact hterm r)
              _ = ∑' r, ((PMF.uniformOfFintype spec.Range) r * (if r ∈ B then (1 : ℝ≥0∞) else 0)
                    + (PMF.uniformOfFintype spec.Range) r * C) := by simp_rw [mul_add]
              _ = (∑' r, (PMF.uniformOfFintype spec.Range) r * (if r ∈ B then (1 : ℝ≥0∞) else 0))
                    + (∑' r, (PMF.uniformOfFintype spec.Range) r * C) := ENNReal.tsum_add
              _ ≤ (log.length : ℝ≥0∞) / N + C := by
                  refine add_le_add ?_ (le_of_eq ?_)
                  · -- first sum = B.card / N ≤ m / N
                    rw [tsum_fintype]
                    simp_rw [PMF.uniformOfFintype_apply, ← hN]
                    rw [← Finset.mul_sum, ENNReal.div_eq_inv_mul]
                    gcongr
                    calc ∑ r : spec.Range, (if r ∈ B then (1 : ℝ≥0∞) else 0)
                        = (B.card : ℝ≥0∞) := by simp
                      _ ≤ (log.length : ℝ≥0∞) := hBcard
                  · -- second sum = C
                    rw [tsum_fintype]
                    simp_rw [PMF.uniformOfFintype_apply, ← hN]
                    rw [← Finset.sum_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hN,
                      ENNReal.mul_inv_cancel hcard hcardtop, one_mul]
          refine hsum.trans (le_of_eq ?_)
          -- m/N + (∑ Ico (m+1) q)/N = (∑ Ico m q)/N
          rw [hC, ENNReal.div_add_div_same]
          congr 1
          rw [← Finset.insert_Ico_succ_left_eq_Ico hmlt,
            Finset.sum_insert (by simp), Order.succ_eq_add_one]

/-- **Trace collision bound for Merkle random oracles.** A computation spending
    at most `q` queries to a `κ`-bit random oracle produces a colliding trace
    with probability at most `collisionBound κ q = q(q-1)/2^(κ+1)`. -/
theorem coupling_trace_le_collisionBound {κ : Nat} {α : Type}
    (c : OracleComp (ROHasher.MerkleROSpec κ) α) (q : Nat)
    (hbud : OracleComp.QueryBudget c q) :
    (c.run QueryLog.empty).toOuterMeasure {p | QueryLog.hasCollision p.2}
      ≤ collisionBound κ q := by
  have hemp : ¬ QueryLog.hasCollision (QueryLog.empty : QueryLog (ROHasher.MerkleROSpec κ)) := by
    simp [QueryLog.hasCollision, QueryLog.empty]
  have h := run_coll_le q c QueryLog.empty hemp hbud
  have hlen : (QueryLog.empty : QueryLog (ROHasher.MerkleROSpec κ)).length = 0 := rfl
  rw [hlen] at h
  have hcard : Fintype.card (ROHasher.MerkleROSpec κ).Range = 2 ^ κ := by
    show Fintype.card (List.Vector Bool κ) = 2 ^ κ
    rw [Fintype.card_congr (Equiv.vectorEquivFin Bool κ), Fintype.card_fun,
      Fintype.card_fin, Fintype.card_bool]
  rw [hcard] at h
  refine h.trans (le_of_eq ?_)
  rw [← Finset.range_eq_Ico]
  unfold collisionBound
  have ha0 : (2 : ℝ≥0∞) ^ (κ + 1) ≠ 0 := by positivity
  have haT : (2 : ℝ≥0∞) ^ (κ + 1) ≠ ∞ := by apply ENNReal.pow_ne_top; simp
  have hb0 : ((2 ^ κ : ℕ) : ℝ≥0∞) ≠ 0 := by positivity
  have hbT : ((2 ^ κ : ℕ) : ℝ≥0∞) ≠ ∞ := by simp
  rw [ENNReal.div_eq_div_iff ha0 haT hb0 hbT,
    show (2 : ℝ≥0∞) ^ (κ + 1) = ((2 ^ κ : ℕ) : ℝ≥0∞) * 2 by push_cast; rw [pow_succ],
    mul_assoc]
  congr 1
  rw [mul_comm]
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq; simp
  · have hq1 : 1 ≤ q := hq
    rw [show (q : ℝ≥0∞) * ((q : ℝ≥0∞) - 1) = ((q * (q - 1) : ℕ) : ℝ≥0∞) by
          push_cast [Nat.cast_sub hq1]; ring,
      ← Nat.cast_sum, ← Nat.cast_two, ← Nat.cast_mul, Nat.cast_inj]
    exact Finset.sum_range_id_mul_two q

end VectorCommitment.Probability
