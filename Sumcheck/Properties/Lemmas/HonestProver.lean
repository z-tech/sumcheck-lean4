import Sumcheck.Src.CMvPolynomial
import Sumcheck.Src.Prover
import Sumcheck.Src.Transcript
import Sumcheck.Src.Hypercube
import Sumcheck.Src.Verifier

import Sumcheck.Properties.Events.BadRound

import Sumcheck.Properties.Lemmas.Eval
import Sumcheck.Properties.Lemmas.Monomials
import Sumcheck.Properties.Lemmas.HonestProverCore  -- Re-export core lemmas

noncomputable def empty_open_assignment
  {𝔽 : Type _} {n : ℕ} [Field 𝔽]
  (i : Fin n) (hopen : num_open_vars (n := n) i = 0) :
  Fin (num_open_vars (n := n) i) → 𝔽 :=
by
  -- build it at Fin 0, then transport along hopen.symm : 0 = num_open_vars i
  refine Eq.ndrec (motive := fun m => Fin m → 𝔽) (fun x : Fin 0 => nomatch x) hopen.symm

lemma honest_right_map_zero
  {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  {n : ℕ} (i : Fin n)
  (b : Fin (num_open_vars (n := n) i) → 𝔽) :
  honest_right_map (𝔽 := 𝔽) (n := n) i b 0 = x0 (𝔽 := 𝔽) := by
  classical
  -- unfold and reduce the match on 0
  unfold honest_right_map
  rfl

lemma eval_honest_right_map_succ
  {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  {n : ℕ} (i : Fin n)
  (a : 𝔽)
  (b : Fin (num_open_vars (n := n) i) → 𝔽)
  (t : Fin (num_open_vars (n := n) i)) :
  CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a)
      (honest_right_map (𝔽 := 𝔽) (n := n) i b t.succ)
    = b t := by
  classical
  -- don't use Fin.cases here (t is Fin open, not Fin (open+1))
  cases t with
  | mk tv th =>
      -- now simp can reduce the match on tv.succ and the Fin.mk proof field mismatch vanishes
      simp [honest_right_map, Fin.succ, c1]
      show CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a) (CPoly.CMvPolynomial.C (b ⟨tv, _⟩)) = b ⟨tv, _⟩
      exact CPoly.eval_C _ _

lemma eval_honest_right_map
  {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  {n : ℕ} (i : Fin n)
  (a : 𝔽)
  (b : Fin (num_open_vars (n := n) i) → 𝔽)
  (t : Fin (num_open_vars (n := n) i + 1)) :
  CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a)
      (honest_right_map (𝔽 := 𝔽) (n := n) i b t)
    =
  Fin.cases a b t := by
  classical
  cases t using Fin.cases with
  | zero =>
      -- t = 0
      -- rewrite honest_right_map ... 0 = x0, then eval_x0
      rw [honest_right_map_zero (𝔽 := 𝔽) (i := i) (b := b)]
      -- RHS is `a`
      simpa using (CPoly.eval_x0 (𝔽 := 𝔽) a)
  | succ t =>
      -- t = succ t
      -- RHS is `b t`
      simpa using (eval_honest_right_map_succ (𝔽 := 𝔽) (i := i) (a := a) (b := b) (t := t))

lemma eval_addCases_honest_right_map
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (r : Fin n → 𝔽)
  (i : Fin n)
  (a : 𝔽)
  (b : Fin (num_open_vars (n := n) i) → 𝔽)
  (j : Fin n) :
  CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a)
      (Fin.addCases
        (fun t : Fin i.val =>
          CPoly.Lawful.C (n := 1) (challenge_subset r i t))
        (honest_right_map (𝔽 := 𝔽) (n := n) i b)
        (Fin.cast (honest_split_eq (n := n) i).symm j))
    =
  Fin.addCases
    (fun t : Fin i.val => r ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩)
    (fun t : Fin (num_open_vars (n := n) i + 1) => Fin.cases a b t)
    (Fin.cast (honest_split_eq (n := n) i).symm j) := by
  classical
  -- Case split on which side `Fin.addCases` takes.
  -- This produces exactly the two branches we want.
  cases h : (Fin.cast (honest_split_eq (n := n) i).symm j) using Fin.addCases with
  | left t =>
      -- left branch: we are evaluating a constant polynomial `C (...)`
      -- and RHS is the corresponding r ⟨t, _⟩.
      simp [Fin.addCases, challenge_subset]
      show CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a) (CPoly.CMvPolynomial.C _) = _
      exact CPoly.eval_C _ _
  | right t =>
      -- right branch: use your `eval_honest_right_map`
      -- RHS is `Fin.cases a b t`
      simpa [Fin.addCases, addCasesFun, h] using
        (eval_honest_right_map (𝔽 := 𝔽) (i := i) (a := a) (b := b)
          (t := t))

lemma eval_honest_combined_map_eq_addCasesFun
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (r : Fin n → 𝔽) (i : Fin n) (a : 𝔽)
  (b : Fin (num_open_vars (n := n) i) → 𝔽) :
  (fun j : Fin n =>
      CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a)
        (honest_combined_map (𝔽 := 𝔽) (n := n) i (challenge_subset r i) b j))
  =
  (fun j : Fin n =>
      addCasesFun (α := 𝔽)
        (fun t : Fin i.val => r ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩)
        (fun t : Fin (num_open_vars (n := n) i + 1) => Fin.cases a b t)
        (Fin.cast (honest_split_eq (n := n) i).symm j)) := by
  classical
  funext j
  -- unfold combined map (it is addCases of constants + honest_right_map)
  -- then apply your lemma
  simpa [honest_combined_map_def, addCasesFun] using
    (eval_addCases_honest_right_map (𝔽 := 𝔽) (r := r) (i := i) (a := a) (b := b) (j := j))

-- ============================================================================
-- Lemmas that CAN be in Lemmas/ (not used by Lemmas/Degree.lean, no cycle)
-- ============================================================================

lemma honest_right_map_succ
  {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  {n : ℕ} (i : Fin n)
  (b : Fin (num_open_vars (n := n) i) → 𝔽)
  (j : ℕ) (hj : j + 1 < num_open_vars (n := n) i + 1) :
  honest_right_map (𝔽 := 𝔽) (n := n) i b ⟨j + 1, hj⟩ =
    c1 (b ⟨j, Nat.lt_of_succ_lt_succ hj⟩) := by
  simp [honest_right_map]

@[simp] lemma honest_prover_message_at_def
  {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  {n : ℕ}
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (i : Fin n)
  (challenges : Fin i.val → 𝔽) :
  honest_prover_message_at domain (𝔽 := 𝔽) (n := n) p i challenges
    =
  sum_over_domain_recursive (𝔽 := 𝔽) (β := CPoly.CMvPolynomial 1 𝔽)
    domain
    (add := fun a b =>
      @HAdd.hAdd
        (CPoly.CMvPolynomial 1 𝔽) (CPoly.CMvPolynomial 1 𝔽) (CPoly.CMvPolynomial 1 𝔽)
        instHAdd a b)
    (zero := c1 (𝔽 := 𝔽) 0)
    (m := num_open_vars (n := n) i)
    (F := fun b =>
      CPoly.eval₂Poly c1 (honest_combined_map (𝔽 := 𝔽) (n := n) i challenges b) p) := by
  rfl
