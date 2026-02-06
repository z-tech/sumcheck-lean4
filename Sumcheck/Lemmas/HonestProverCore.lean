/-
  HonestProverCore.lean

  Core lemmas about honest prover data structures.
  This module exists to break a circular import:
    HonestProver → Eval2 → Fin → Degree → HonestProver

  By having Degree.lean import this module instead of the full Lemmas/HonestProver,
  we avoid the cycle.
-/

import Sumcheck.Src.CMvPolynomial
import Sumcheck.Src.HonestProver
import Sumcheck.Src.Hypercube

-- ============================================================================
-- Lemmas about honest_combined_map used by Lemmas/Degree.lean
-- ============================================================================

lemma honest_combined_map_def
  {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  {n : ℕ} (i : Fin n)
  (challenges : Fin i.val → 𝔽)
  (b : Fin (honest_num_open_vars (n := n) i) → 𝔽)
  (j : Fin n) :
  honest_combined_map (𝔽 := 𝔽) (n := n) i challenges b j =
    Fin.addCases (m := i.val) (n := honest_num_open_vars (n := n) i + 1)
      (motive := fun _ => CPoly.CMvPolynomial 1 𝔽)
      (fun t : Fin i.val => c1 (challenges t))
      (honest_right_map (𝔽 := 𝔽) (n := n) i b)
      (Fin.cast (honest_split_eq (n := n) i).symm j) := by
  -- Unfold the definition through append_variable_assignments
  simp [honest_combined_map, append_variable_assignments]

lemma honest_combined_map_left
  {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  {n : ℕ} (i : Fin n)
  (challenges : Fin i.val → 𝔽)
  (b : Fin (honest_num_open_vars (n := n) i) → 𝔽)
  (t : Fin i.val) :
  honest_combined_map (𝔽 := 𝔽) (n := n) i challenges b
      (Fin.cast (honest_split_eq (n := n) i) (Fin.castAdd (honest_num_open_vars (n := n) i + 1) t))
    = c1 (challenges t) := by
  simp [honest_combined_map_def (i := i) (challenges := challenges) (b := b)]

lemma honest_combined_map_right
  {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  {n : ℕ} (i : Fin n)
  (challenges : Fin i.val → 𝔽)
  (b : Fin (honest_num_open_vars (n := n) i) → 𝔽)
  (t : Fin (honest_num_open_vars (n := n) i + 1)) :
  honest_combined_map (𝔽 := 𝔽) (n := n) i challenges b
      (Fin.cast (honest_split_eq (n := n) i) (Fin.natAdd i.val t))
    = honest_right_map (𝔽 := 𝔽) (n := n) i b t := by
  simp [honest_combined_map_def (i := i) (challenges := challenges) (b := b)]

lemma honest_combined_map_current_is_x0
  {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  {n : ℕ} (i : Fin n)
  (challenges : Fin i.val → 𝔽)
  (b : Fin (honest_num_open_vars (n := n) i) → 𝔽) :
  honest_combined_map (𝔽 := 𝔽) (n := n) i challenges b
      (Fin.cast (honest_split_eq (n := n) i) (Fin.natAdd i.val ⟨0, Nat.succ_pos _⟩))
    = x0 := by
  let t : Fin (honest_num_open_vars (n := n) i + 1) := ⟨0, Nat.succ_pos _⟩
  have h :=
    honest_combined_map_right
      (𝔽 := 𝔽) (n := n) (i := i) (challenges := challenges) (b := b) (t := t)
  simpa [t, honest_right_map] using h

lemma honest_current_index_eq (i : Fin n) :
  Fin.cast (honest_split_eq (n := n) i)
      (Fin.natAdd i.val ⟨0, Nat.succ_pos _⟩)
    = i := by
  ext
  simp

lemma honest_combined_map_at_i_is_x0
  {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  {n : ℕ} (i : Fin n)
  (challenges : Fin i.val → 𝔽)
  (b : Fin (honest_num_open_vars (n := n) i) → 𝔽) :
  honest_combined_map (𝔽 := 𝔽) (n := n) i challenges b i = x0 := by
  have :=
    honest_combined_map_current_is_x0
      (𝔽 := 𝔽) (n := n) (i := i) (challenges := challenges) (b := b)
  simpa [honest_current_index_eq (n := n) i] using this
