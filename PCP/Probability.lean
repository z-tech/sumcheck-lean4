/-
Copyright (c) 2026 LeanStuff contributors. All rights reserved.
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Elementary probability inequalities for the PCP / Kilian analysis

This file collects reusable real-analysis inequalities used in the
soundness analysis of Kilian's protocol
([eprint 2024/1434](https://eprint.iacr.org/2024/1434)). The headline
fact is `delta_compl_pow_le`, which bounds the maximum of `δ(1-δ)^N`
over `δ ∈ [0,1]` and is the elementary inequality at the heart of the
"missing positions" case (§5.1, paper page 26): for the per-position
marginal `δ_q · (1 - δ_q)^N ≤ 1/N`, summed over the `ℓ` proof positions
to bound the "missing in `Q̃`" probability by `ℓ/N = ε`.

## References

* Mathlib's two-point weighted AM-GM:
  `Real.geom_mean_le_arith_mean2_weighted`.
-/

open Real

/-- Helper: for `0 ≤ δ ≤ 1` and `1 ≤ N`, we have `N * δ * (1-δ)^N ≤ 1`.
Proved via two-point weighted AM-GM with weights `N/(N+1)` and `1/(N+1)`
on values `(1-δ)` and `Nδ`. -/
private lemma N_delta_one_sub_pow_le_one
    (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) * δ * (1 - δ) ^ N ≤ 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1pos : (0 : ℝ) < (N : ℝ) + 1 := by linarith
  have hN1ne : ((N : ℝ) + 1) ≠ 0 := ne_of_gt hN1pos
  -- Weights and values for AM-GM (no `set` so let-folding doesn't interfere)
  have hw₁_nn : (0 : ℝ) ≤ (N : ℝ) / ((N : ℝ) + 1) :=
    div_nonneg (le_of_lt hNpos) (le_of_lt hN1pos)
  have hw₂_nn : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) :=
    div_nonneg zero_le_one (le_of_lt hN1pos)
  have hw_sum : (N : ℝ) / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1) = 1 := by
    field_simp
  have hp₁_nn : (0 : ℝ) ≤ 1 - δ := by linarith
  have hp₂_nn : (0 : ℝ) ≤ (N : ℝ) * δ := mul_nonneg (le_of_lt hNpos) h0
  -- AM-GM: (1-δ)^(N/(N+1)) * (Nδ)^(1/(N+1)) ≤ (N/(N+1))(1-δ) + (1/(N+1))(Nδ)
  have amgm :
      (1 - δ) ^ ((N : ℝ) / ((N : ℝ) + 1)) * ((N : ℝ) * δ) ^ (1 / ((N : ℝ) + 1))
        ≤ (N : ℝ) / ((N : ℝ) + 1) * (1 - δ) + 1 / ((N : ℝ) + 1) * ((N : ℝ) * δ) :=
    Real.geom_mean_le_arith_mean2_weighted hw₁_nn hw₂_nn hp₁_nn hp₂_nn hw_sum
  -- Bound the RHS by N/(N+1)
  have rhs_eq :
      (N : ℝ) / ((N : ℝ) + 1) * (1 - δ) + 1 / ((N : ℝ) + 1) * ((N : ℝ) * δ)
        = (N : ℝ) / ((N : ℝ) + 1) := by
    field_simp
    ring
  rw [rhs_eq] at amgm
  -- N/(N+1) ≤ 1
  have NN1_le_one : (N : ℝ) / ((N : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hN1pos]; linarith
  -- So the geometric-mean LHS is ≤ 1
  have key :
      (1 - δ) ^ ((N : ℝ) / ((N : ℝ) + 1)) * ((N : ℝ) * δ) ^ (1 / ((N : ℝ) + 1)) ≤ 1 :=
    le_trans amgm NN1_le_one
  -- Both factors are nonneg
  have lhs_nn :
      0 ≤ (1 - δ) ^ ((N : ℝ) / ((N : ℝ) + 1)) * ((N : ℝ) * δ) ^ (1 / ((N : ℝ) + 1)) :=
    mul_nonneg (Real.rpow_nonneg hp₁_nn _) (Real.rpow_nonneg hp₂_nn _)
  -- Raise to (N+1)-th power
  have key_pow :
      ((1 - δ) ^ ((N : ℝ) / ((N : ℝ) + 1)) * ((N : ℝ) * δ) ^ (1 / ((N : ℝ) + 1)))
        ^ ((N : ℕ) + 1) ≤ 1 := by
    have := pow_le_pow_left₀ lhs_nn key ((N : ℕ) + 1)
    simpa using this
  -- Show this Nth-power expression equals (1-δ)^N * (Nδ)
  have expand :
      ((1 - δ) ^ ((N : ℝ) / ((N : ℝ) + 1)) * ((N : ℝ) * δ) ^ (1 / ((N : ℝ) + 1)))
        ^ ((N : ℕ) + 1)
        = (1 - δ) ^ N * ((N : ℝ) * δ) := by
    rw [show ((1 - δ) ^ ((N : ℝ) / ((N : ℝ) + 1)) * ((N : ℝ) * δ) ^ (1 / ((N : ℝ) + 1)))
          ^ ((N : ℕ) + 1)
        = ((1 - δ) ^ ((N : ℝ) / ((N : ℝ) + 1)) * ((N : ℝ) * δ) ^ (1 / ((N : ℝ) + 1)))
          ^ (((N : ℕ) + 1 : ℕ) : ℝ)
        from (Real.rpow_natCast _ _).symm]
    rw [Real.mul_rpow (Real.rpow_nonneg hp₁_nn _) (Real.rpow_nonneg hp₂_nn _)]
    rw [← Real.rpow_mul hp₁_nn, ← Real.rpow_mul hp₂_nn]
    have e1 : (N : ℝ) / ((N : ℝ) + 1) * (((N : ℕ) + 1 : ℕ) : ℝ) = (N : ℝ) := by
      push_cast; field_simp
    have e2 : 1 / ((N : ℝ) + 1) * (((N : ℕ) + 1 : ℕ) : ℝ) = 1 := by
      push_cast; field_simp
    rw [e1, e2, Real.rpow_one, Real.rpow_natCast]
  rw [expand] at key_pow
  have : (1 - δ) ^ N * ((N : ℝ) * δ) = (N : ℝ) * δ * (1 - δ) ^ N := by ring
  linarith [key_pow, this]

/-- **`δ · (1 - δ)^N ≤ 1/N`** for `δ ∈ [0,1]` and `N ≥ 1`.

This is the elementary inequality at the core of the missing-position
bound (paper §5.1): with `δ_q := Pr_ρ[q ∈ verifierQueries x ρ]` and
`rhos` consisting of `N` i.i.d. samples, the marginal probability that
`q ∈ Q ∧ q ∉ Q̃` equals `δ_q · (1 - δ_q)^N`, which this lemma bounds by
`1/N`. Summing over the `ℓ` proof positions then gives the `ℓ/N = ε`
bound on the missing-position event.

Proved via two-point weighted AM-GM (no calculus). -/
theorem delta_compl_pow_le (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (N : ℕ) (hN : 1 ≤ N) :
    δ * (1 - δ)^N ≤ 1 / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN_le_one := N_delta_one_sub_pow_le_one δ h0 h1 N hN
  rw [le_div_iff₀ hNpos]
  nlinarith [hN_le_one]
