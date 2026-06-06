import VectorCommitment.Properties.Probability.RandomOracle
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Probability.Distributions.Uniform

/-!
# RO probability lemmas: the birthday collision bound

The quantitative core every ROM-instance file (`BindingROM`,
`ExtractabilityROM`, `HidingROM`, `EquivocationROM`) reduces to:

* **`birthdayBound`** — among `n` independent uniform samples from a
  finite set `R`, the probability that two of the samples coincide is
  at most `n · (n - 1) / (2 · |R|)`. Specialised to `R = List.Vector
  Bool κ` this is the classic `n² / 2^(κ+1)` form.

Proved by a union bound over the `n(n-1)/2` unordered coordinate pairs,
each colliding with probability `1/|R|` (`prob_pair`).
-/

namespace VectorCommitment.Probability

open OracleComp

/-- The concrete error expression every ROM instance carries.
    `κ` is the digest bit-length; `q` is the adversary's RO query budget. -/
noncomputable def collisionBound (κ q : Nat) : ENNReal :=
  (q * (q - 1) : ENNReal) / 2 ^ (κ + 1)

section BirthdayBound
open scoped ENNReal
open Finset MeasureTheory

/-- Functions `Fin n → R` agreeing at two distinct coordinates `i ≠ j` are in
    bijection with arbitrary functions on the `n-1` coordinates `≠ j`. -/
private def tieEquiv {R : Type} {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    {f : Fin n → R // f i = f j} ≃ ({k : Fin n // k ≠ j} → R) where
  toFun p := fun k => p.1 k.1
  invFun g := ⟨fun k => if h : k = j then g ⟨i, hij⟩ else g ⟨k, h⟩, by
    show (if h : i = j then g ⟨i, hij⟩ else g ⟨i, h⟩)
       = (if h : j = j then g ⟨i, hij⟩ else g ⟨j, h⟩)
    rw [dif_neg hij, dif_pos rfl]⟩
  left_inv := by
    rintro ⟨f, hf⟩
    apply Subtype.ext
    funext k
    show (if h : k = j then f i else f k) = f k
    by_cases h : k = j
    · subst h; rw [dif_pos rfl]; exact hf
    · rw [dif_neg h]
  right_inv := by
    intro g
    funext k
    obtain ⟨k, hk⟩ := k
    show (if h : k = j then g ⟨i, hij⟩ else g ⟨k, h⟩) = g ⟨k, hk⟩
    rw [dif_neg hk]

/-- The number of functions tying two distinct coordinates is `|R|^(n-1)`. -/
private lemma card_tie {R : Type} [Fintype R] [DecidableEq R] {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) :
    Fintype.card {f : Fin n → R // f i = f j} = Fintype.card R ^ (n - 1) := by
  rw [Fintype.card_congr (tieEquiv i j hij), Fintype.card_fun]
  congr 1
  simp only [ne_eq]
  rw [Fintype.card_subtype_compl (fun k => k = j), Fintype.card_subtype_eq,
    Fintype.card_fin]

/-- The per-pair collision probability under the uniform PMF on `Fin n → R`
    is exactly `1/|R|` (for `i ≠ j`). -/
private lemma prob_pair {R : Type} [Fintype R] [Nonempty R] [DecidableEq R] {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) :
    (PMF.uniformOfFintype (Fin n → R)).toOuterMeasure {f | f i = f j}
      = 1 / (Fintype.card R : ℝ≥0∞) := by
  haveI : Fintype {f : Fin n → R // f i = f j} := Subtype.fintype _
  have hn : 0 < n := Nat.pos_of_ne_zero (fun h => by subst h; exact i.elim0)
  have hc0 : (Fintype.card R : ℝ≥0∞) ≠ 0 := by simp [Fintype.card_ne_zero]
  have hctop : (Fintype.card R : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hpow0 : (Fintype.card R : ℝ≥0∞) ^ (n - 1) ≠ 0 := pow_ne_zero _ hc0
  have hpowtop : (Fintype.card R : ℝ≥0∞) ^ (n - 1) ≠ ⊤ := ENNReal.pow_ne_top hctop
  have hsplit : (Fintype.card R : ℝ≥0∞) ^ n
      = (Fintype.card R : ℝ≥0∞) ^ (n - 1) * (Fintype.card R) := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  rw [PMF.toOuterMeasure_uniformOfFintype_apply,
    show Fintype.card ↥{f : Fin n → R | f i = f j} = Fintype.card R ^ (n - 1)
      from card_tie i j hij,
    Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_pow, hsplit,
    div_eq_mul_inv, ENNReal.mul_inv (Or.inl hpow0) (Or.inl hpowtop), ← mul_assoc,
    ENNReal.mul_inv_cancel hpow0 hpowtop, one_mul, one_div]

/-- **Birthday bound.** Among `n` independent uniform samples from a
    finite, nonempty range `R`, the probability that some pair of
    samples coincides is at most `n · (n - 1) / (2 · |R|)`.

    *Specialisation:* when `R = List.Vector Bool κ` (`|R| = 2^κ`) the
    bound becomes `collisionBound κ n`.

    *Proof:* union bound over the `n(n-1)/2` unordered pairs `{i<j}`, each
    coinciding with probability `1/|R|` (`prob_pair`). -/
theorem birthdayBound (n : Nat) {R : Type} [Fintype R] [Nonempty R] :
    (PMF.uniformOfFintype (Fin n → R)).toOuterMeasure
      {f | ∃ i j : Fin n, i ≠ j ∧ f i = f j}
      ≤ (n * (n - 1) : ENNReal) / (2 * Fintype.card R) := by
  classical
  set pairs : Finset (Fin n × Fin n) := univ.filter (fun p => p.1 < p.2) with hpairs
  have hcover : {f : Fin n → R | ∃ i j, i ≠ j ∧ f i = f j}
      ⊆ ⋃ p ∈ pairs, {f : Fin n → R | f p.1 = f p.2} := by
    intro f hf
    obtain ⟨i, j, hij, hfij⟩ := hf
    rcases lt_or_gt_of_ne hij with h | h
    · refine Set.mem_iUnion₂.mpr ⟨(i, j), ?_, hfij⟩
      rw [hpairs]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    · refine Set.mem_iUnion₂.mpr ⟨(j, i), ?_, hfij.symm⟩
      rw [hpairs]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
  have h2 : pairs.card * 2 = n * (n - 1) := by
    have hcount : ∀ b : Fin n,
        (univ.filter (fun a : Fin n => a < b)).card = (b : ℕ) := by
      intro b
      rw [show univ.filter (fun a : Fin n => a < b) = Finset.Iio b from by
        ext a; simp [Finset.mem_Iio], Fin.card_Iio]
    rw [hpairs, Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
    simp_rw [← Finset.card_filter, hcount]
    rw [Fin.sum_univ_eq_sum_range (fun i => i) n]
    exact Finset.sum_range_id_mul_two n
  calc (PMF.uniformOfFintype (Fin n → R)).toOuterMeasure
          {f | ∃ i j : Fin n, i ≠ j ∧ f i = f j}
      ≤ (PMF.uniformOfFintype (Fin n → R)).toOuterMeasure
          (⋃ p ∈ pairs, {f | f p.1 = f p.2}) :=
        measure_mono hcover
    _ ≤ ∑ p ∈ pairs,
          (PMF.uniformOfFintype (Fin n → R)).toOuterMeasure {f | f p.1 = f p.2} :=
        measure_biUnion_finset_le pairs _
    _ = ∑ _p ∈ pairs, (1 / (Fintype.card R : ℝ≥0∞)) := by
        refine Finset.sum_congr rfl (fun p hp => ?_)
        rw [hpairs, Finset.mem_filter] at hp
        exact prob_pair p.1 p.2 (ne_of_lt hp.2)
    _ = (pairs.card : ℝ≥0∞) * (1 / Fintype.card R) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (n * (n - 1) : ENNReal) / (2 * Fintype.card R) := by
        have hcast : (pairs.card : ℝ≥0∞) * 2 = (n : ℝ≥0∞) * ((n : ℝ≥0∞) - 1) := by
          rcases Nat.eq_zero_or_pos n with hn0 | hn1
          · subst hn0; simp
          · have e : ((pairs.card * 2 : ℕ) : ℝ≥0∞) = ((n * (n - 1) : ℕ) : ℝ≥0∞) :=
              congrArg Nat.cast h2
            push_cast [Nat.cast_sub hn1] at e
            exact e
        refine le_of_eq ?_
        rw [mul_one_div, ← hcast, mul_comm (pairs.card : ℝ≥0∞) 2,
          ENNReal.mul_div_mul_left _ _ (by simp) (by simp)]

end BirthdayBound

/-- Specialisation to κ-bit digests: the birthday bound is exactly
    `collisionBound κ n = n(n-1)/2^(κ+1)`. Reduction to `birthdayBound`. -/
theorem birthdayBound_kappa (κ n : Nat) {R : Type}
    [Fintype R] [Nonempty R] (h_card : Fintype.card R = 2 ^ κ) :
    (PMF.uniformOfFintype (Fin n → R)).toOuterMeasure
      {f | ∃ i j : Fin n, i ≠ j ∧ f i = f j}
      ≤ collisionBound κ n := by
  -- Reduce to `birthdayBound`, then rewrite `2 * |R| = 2^(κ+1)` via h_card.
  refine (birthdayBound n).trans ?_
  unfold collisionBound
  rw [h_card]
  -- Goal: ↑n * (↑n - 1) / (2 * ↑(2^κ)) ≤ ↑n * (↑n - 1) / 2^(κ+1)
  -- Reduce to equality of denominators.
  have h_denom : (2 : ENNReal) * ((2 ^ κ : ℕ) : ENNReal) = (2 : ENNReal) ^ (κ + 1) := by
    push_cast
    rw [pow_succ, mul_comm]
  rw [h_denom]

end VectorCommitment.Probability
