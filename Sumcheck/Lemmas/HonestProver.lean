import Sumcheck.Src.CMvPolynomial
import Sumcheck.Src.HonestProver
import Sumcheck.Src.HonestTranscript
import Sumcheck.Src.Hypercube
import Sumcheck.Src.Verifier

import Sumcheck.Events.BadRound

import Sumcheck.Lemmas.Eval2
import Sumcheck.Lemmas.Monomials

noncomputable def empty_open_assignment
  {𝔽 : Type _} {n : ℕ} [Field 𝔽]
  (i : Fin n) (hopen : honest_num_open_vars (n := n) i = 0) :
  Fin (honest_num_open_vars (n := n) i) → 𝔽 :=
by
  -- build it at Fin 0, then transport along hopen.symm : 0 = honest_num_open_vars i
  refine Eq.ndrec (motive := fun m => Fin m → 𝔽) (fun x : Fin 0 => nomatch x) hopen.symm

lemma honest_right_map_zero
  {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  {n : ℕ} (i : Fin n)
  (b : Fin (honest_num_open_vars (n := n) i) → 𝔽) :
  honest_right_map (𝔽 := 𝔽) (n := n) i b 0 = x0 (𝔽 := 𝔽) := by
  classical
  -- unfold and reduce the match on 0
  unfold honest_right_map
  rfl

lemma eval₂_honest_right_map_succ
  {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  {n : ℕ} (i : Fin n)
  (a : 𝔽)
  (b : Fin (honest_num_open_vars (n := n) i) → 𝔽)
  (t : Fin (honest_num_open_vars (n := n) i)) :
  CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
      (RingHom.id 𝔽) (fun _ : Fin 1 => a)
      (honest_right_map (𝔽 := 𝔽) (n := n) i b t.succ)
    = b t := by
  classical
  -- don't use Fin.cases here (t is Fin open, not Fin (open+1))
  cases t with
  | mk tv th =>
      -- now simp can reduce the match on tv.succ and the Fin.mk proof field mismatch vanishes
      simp [honest_right_map, Fin.succ, c1, CPoly.eval₂_Lawful_C]

lemma eval₂_honest_right_map
  {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  {n : ℕ} (i : Fin n)
  (a : 𝔽)
  (b : Fin (honest_num_open_vars (n := n) i) → 𝔽)
  (t : Fin (honest_num_open_vars (n := n) i + 1)) :
  CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
      (RingHom.id 𝔽) (fun _ : Fin 1 => a)
      (honest_right_map (𝔽 := 𝔽) (n := n) i b t)
    =
  Fin.cases a b t := by
  classical
  cases t using Fin.cases with
  | zero =>
      -- t = 0
      -- rewrite honest_right_map ... 0 = x0, then eval₂_x0
      rw [honest_right_map_zero (𝔽 := 𝔽) (i := i) (b := b)]
      -- RHS is `a`
      simpa using (CPoly.eval₂_x0 (𝔽 := 𝔽) a)
  | succ t =>
      -- t = succ t
      -- RHS is `b t`
      simpa using (eval₂_honest_right_map_succ (𝔽 := 𝔽) (i := i) (a := a) (b := b) (t := t))

lemma eval₂_addCases_honest_right_map
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (r : Fin n → 𝔽)
  (i : Fin n)
  (a : 𝔽)
  (b : Fin (honest_num_open_vars (n := n) i) → 𝔽)
  (j : Fin n) :
  CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
      (RingHom.id 𝔽) (fun _ : Fin 1 => a)
      (Fin.addCases
        (fun t : Fin i.val =>
          CPoly.Lawful.C (n := 1) (challenge_subset r i t))
        (honest_right_map (𝔽 := 𝔽) (n := n) i b)
        (Fin.cast (honest_split_eq (n := n) i).symm j))
    =
  Fin.addCases
    (fun t : Fin i.val => r ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩)
    (fun t : Fin (honest_num_open_vars (n := n) i + 1) => Fin.cases a b t)
    (Fin.cast (honest_split_eq (n := n) i).symm j) := by
  classical
  -- Case split on which side `Fin.addCases` takes.
  -- This produces exactly the two branches we want.
  cases h : (Fin.cast (honest_split_eq (n := n) i).symm j) using Fin.addCases with
  | left t =>
      -- left branch: we are evaluating a constant polynomial `C (...)`
      -- and RHS is the corresponding r ⟨t, _⟩.
      simp [Fin.addCases, CPoly.eval₂_Lawful_C, challenge_subset]
  | right t =>
      -- right branch: use your `eval₂_honest_right_map`
      -- RHS is `Fin.cases a b t`
      simpa [Fin.addCases, addCasesFun, h] using
        (eval₂_honest_right_map (𝔽 := 𝔽) (i := i) (a := a) (b := b)
          (t := t))

lemma eval₂_honest_combined_map_eq_addCasesFun
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (r : Fin n → 𝔽) (i : Fin n) (a : 𝔽)
  (b : Fin (honest_num_open_vars (n := n) i) → 𝔽) :
  (fun j : Fin n =>
      CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
        (RingHom.id 𝔽) (fun _ : Fin 1 => a)
        (honest_combined_map (𝔽 := 𝔽) (n := n) i (challenge_subset r i) b j))
  =
  (fun j : Fin n =>
      addCasesFun (α := 𝔽)
        (fun t : Fin i.val => r ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩)
        (fun t : Fin (honest_num_open_vars (n := n) i + 1) => Fin.cases a b t)
        (Fin.cast (honest_split_eq (n := n) i).symm j)) := by
  classical
  funext j
  -- unfold combined map (it is addCases of constants + honest_right_map)
  -- then apply your lemma
  simpa [honest_combined_map_def, addCasesFun] using
    (eval₂_addCases_honest_right_map (𝔽 := 𝔽) (r := r) (i := i) (a := a) (b := b) (j := j))
