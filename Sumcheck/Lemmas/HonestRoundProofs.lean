/-
  HonestRoundProofs.lean

  Proofs about honest round polynomials, including:
  - eval₂_honest_round_poly_eq_sum_eval
  - honest_num_open_vars_succ
  - honest_step_round
  - honest_last_round
-/

import Sumcheck.Src.HonestTranscript
import Sumcheck.Src.Hypercube
import Sumcheck.Src.Verifier
import Sumcheck.Lemmas.HonestProver
import Sumcheck.Lemmas.Hypercube
import Sumcheck.Lemmas.Eval2
import Sumcheck.Lemmas.Nat
import Sumcheck.Lemmas.Fin

theorem eval₂_honest_round_poly_eq_sum_eval {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽) (r : Fin n → 𝔽) (i : Fin n) (a : 𝔽) :
  CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => a)
      (honest_round_poly (p := p) (ch := r) i)
    =
  sum_over_hypercube_recursive (𝔽 := 𝔽) (β := 𝔽)
    (b0 := (0 : 𝔽)) (b1 := (1 : 𝔽)) (add := (· + ·))
    (m := honest_num_open_vars (n := n) i)
    (fun x =>
      CPoly.CMvPolynomial.eval
        (fun k : Fin n =>
          addCasesFun
            (fun t : Fin i.val => r ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩)
            (fun t : Fin (honest_num_open_vars (n := n) i + 1) => Fin.cases a x t)
            (Fin.cast (honest_split_eq_cast (n := n) i (honest_num_open_vars (n := n) i) rfl).symm k))
        p) := by
  classical
  unfold honest_round_poly
  -- unfold the honest prover polynomial and push eval₂ through the hypercube sum
  simp [CPoly.eval₂_eval₂Poly_c1, eval₂_honest_combined_map_eq_addCasesFun]


theorem honest_num_open_vars_succ {n : ℕ} (i : Fin n) (hlt : i.val.succ < n) :
    honest_num_open_vars (n := n) i
      = honest_num_open_vars (n := n) (⟨i.val.succ, hlt⟩ : Fin n) + 1 := by
  have hNat : n - (i.val + 1) = 1 + (n - (i.val + 2)) := nat_sub_add_two n i.val hlt
  simpa [honest_num_open_vars, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hNat

theorem honest_step_round {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽) (r : Fin n → 𝔽) (i : Fin n)
  (hlt : i.val.succ < n) :
  let j : Fin n := ⟨i.val.succ, hlt⟩
  CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (0 : 𝔽))
      (honest_round_poly (p := p) (ch := r) j)
    +
    CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (1 : 𝔽))
      (honest_round_poly (p := p) (ch := r) j)
    =
    next_claim (𝔽 := 𝔽) (round_challenge := r i) (honest_round_poly (p := p) (ch := r) i) := by
  classical
  simp [next_claim]
  set j : Fin n := ⟨i.val.succ, hlt⟩ with hj

  have h0 :=
    eval₂_honest_round_poly_eq_sum_eval (𝔽 := 𝔽) (n := n) (p := p) (r := r) (i := j) (a := (0 : 𝔽))
  have h1 :=
    eval₂_honest_round_poly_eq_sum_eval (𝔽 := 𝔽) (n := n) (p := p) (r := r) (i := j) (a := (1 : 𝔽))
  have hr :=
    eval₂_honest_round_poly_eq_sum_eval (𝔽 := 𝔽) (n := n) (p := p) (r := r) (i := i) (a := r i)
  rw [h0, h1, hr]

  set openI : ℕ := honest_num_open_vars (n := n) i
  set openJ : ℕ := honest_num_open_vars (n := n) j

  have hm : openI = openJ + 1 := by
    simpa [openI, openJ, hj] using (honest_num_open_vars_succ (n := n) i hlt)

  have hm1 : openJ + 1 + 1 = openI + 1 := by
    simp [hm, Nat.add_assoc]

  let Fi : (Fin openI → 𝔽) → 𝔽 := fun x =>
    CPoly.CMvPolynomial.eval
      (fun k : Fin n =>
        addCasesFun
          (fun t : Fin i.val => r ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩)
          (fun t : Fin (openI + 1) => Fin.cases (r i) x t)
          (Fin.cast (honest_split_eq (n := n) i).symm k))
      p

  let Fj0 : (Fin openJ → 𝔽) → 𝔽 := fun x =>
    CPoly.CMvPolynomial.eval
      (fun k : Fin n =>
        addCasesFun
          (fun t : Fin j.val => r ⟨t.val, Nat.lt_trans t.isLt j.isLt⟩)
          (fun t : Fin (openJ + 1) => Fin.cases (0 : 𝔽) x t)
          (Fin.cast (honest_split_eq (n := n) j).symm k))
      p

  let Fj1 : (Fin openJ → 𝔽) → 𝔽 := fun x =>
    CPoly.CMvPolynomial.eval
      (fun k : Fin n =>
        addCasesFun
          (fun t : Fin j.val => r ⟨t.val, Nat.lt_trans t.isLt j.isLt⟩)
          (fun t : Fin (openJ + 1) => Fin.cases (1 : 𝔽) x t)
          (Fin.cast (honest_split_eq (n := n) j).symm k))
      p

  change
      sum_over_hypercube_recursive (𝔽 := 𝔽) (β := 𝔽)
          (b0 := (0 : 𝔽)) (b1 := (1 : 𝔽)) (add := (· + ·))
          (m := openJ) (fun x => Fj0 x)
        +
        sum_over_hypercube_recursive (𝔽 := 𝔽) (β := 𝔽)
          (b0 := (0 : 𝔽)) (b1 := (1 : 𝔽)) (add := (· + ·))
          (m := openJ) (fun x => Fj1 x)
        =
        sum_over_hypercube_recursive (𝔽 := 𝔽) (β := 𝔽)
          (b0 := (0 : 𝔽)) (b1 := (1 : 𝔽)) (add := (· + ·))
          (m := openI) (fun x => Fi x)

  have hsplit :=
    sum_over_hypercube_recursive_succ_of_hopen (𝔽 := 𝔽) (β := 𝔽)
      (b0 := (0 : 𝔽)) (b1 := (1 : 𝔽)) (add := (· + ·))
      (m := openJ) (m' := openI) hm
      (F := fun x => Fi x)
  rw [hsplit]

  have hbranch0 :
      sum_over_hypercube_recursive (𝔽 := 𝔽) (β := 𝔽)
          (b0 := (0 : 𝔽)) (b1 := (1 : 𝔽)) (add := (· + ·))
          (m := openJ)
          (fun x => Fi ((Fin.cons (0 : 𝔽) x) ∘ Fin.cast hm))
        =
      sum_over_hypercube_recursive (𝔽 := 𝔽) (β := 𝔽)
          (b0 := (0 : 𝔽)) (b1 := (1 : 𝔽)) (add := (· + ·))
          (m := openJ)
          (fun x => Fj0 x) := by
    refine
      sum_over_hypercube_recursive_congr (𝔽 := 𝔽) (β := 𝔽)
        (b0 := (0 : 𝔽)) (b1 := (1 : 𝔽)) (add := (· + ·))
        (m := openJ)
        (F := fun x => Fi ((Fin.cons (0 : 𝔽) x) ∘ Fin.cast hm))
        (G := fun x => Fj0 x)
        ?_
    intro x
    unfold Fi Fj0
    have hpoint :
        (fun k : Fin n =>
            addCasesFun
              (fun t : Fin i.val => r ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩)
              (fun t : Fin (openI + 1) =>
                Fin.cases (r i) ((Fin.cons (0 : 𝔽) x) ∘ Fin.cast hm) t)
              (Fin.cast (honest_split_eq (n := n) i).symm k))
          =
        (fun k : Fin n =>
            addCasesFun
              (fun t : Fin j.val => r ⟨t.val, Nat.lt_trans t.isLt j.isLt⟩)
              (fun t : Fin (openJ + 1) => Fin.cases (0 : 𝔽) x t)
              (Fin.cast (honest_split_eq (n := n) j).symm k)) := by
      funext k
      cases hk : (Fin.cast (honest_split_eq (n := n) j).symm k) using Fin.addCases with
      | left t =>
          cases t using Fin.lastCases with
          | last =>
              have hi :
                  Fin.cast (honest_split_eq (n := n) i).symm k
                    =
                  Fin.natAdd i.val (0 : Fin (honest_num_open_vars (n := n) i + 1)) := by
                apply cast_split_eq_succ_last (n := n) i hlt k
                simpa [hj] using hk
              simp [addCasesFun, hi, openI, openJ]
          | cast t0 =>
              have hi :
                  Fin.cast (honest_split_eq (n := n) i).symm k
                    =
                  Fin.castAdd (honest_num_open_vars (n := n) i + 1) t0 := by
                apply cast_split_eq_succ_castSucc (n := n) i hlt k t0
                simpa [hj] using hk
              simp [addCasesFun, hi, openI, openJ]
      | right t =>
          have hi :
              Fin.cast (honest_split_eq (n := n) i).symm k
                =
              Fin.natAdd i.val (Fin.cast hm1 (Fin.succ t)) := by
            apply
              cast_split_eq_succ_right (n := n) i hlt k t
                (hm1 := by
                  simpa [openI, openJ] using hm1)
            simpa [hj] using hk
          simp [addCasesFun, hi, openI, openJ, Fin.cons, Fin.cases]

    simpa [addCasesFun] using congrArg (fun f => CPoly.CMvPolynomial.eval f p) hpoint

  have hbranch1 :
      sum_over_hypercube_recursive (𝔽 := 𝔽) (β := 𝔽)
          (b0 := (0 : 𝔽)) (b1 := (1 : 𝔽)) (add := (· + ·))
          (m := openJ)
          (fun x => Fi ((Fin.cons (1 : 𝔽) x) ∘ Fin.cast hm))
        =
      sum_over_hypercube_recursive (𝔽 := 𝔽) (β := 𝔽)
          (b0 := (0 : 𝔽)) (b1 := (1 : 𝔽)) (add := (· + ·))
          (m := openJ)
          (fun x => Fj1 x) := by
    refine
      sum_over_hypercube_recursive_congr (𝔽 := 𝔽) (β := 𝔽)
        (b0 := (0 : 𝔽)) (b1 := (1 : 𝔽)) (add := (· + ·))
        (m := openJ)
        (F := fun x => Fi ((Fin.cons (1 : 𝔽) x) ∘ Fin.cast hm))
        (G := fun x => Fj1 x)
        ?_
    intro x
    unfold Fi Fj1
    have hpoint :
        (fun k : Fin n =>
            addCasesFun
              (fun t : Fin i.val => r ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩)
              (fun t : Fin (openI + 1) =>
                Fin.cases (r i) ((Fin.cons (1 : 𝔽) x) ∘ Fin.cast hm) t)
              (Fin.cast (honest_split_eq (n := n) i).symm k))
          =
        (fun k : Fin n =>
            addCasesFun
              (fun t : Fin j.val => r ⟨t.val, Nat.lt_trans t.isLt j.isLt⟩)
              (fun t : Fin (openJ + 1) => Fin.cases (1 : 𝔽) x t)
              (Fin.cast (honest_split_eq (n := n) j).symm k)) := by
      funext k
      cases hk : (Fin.cast (honest_split_eq (n := n) j).symm k) using Fin.addCases with
      | left t =>
          cases t using Fin.lastCases with
          | last =>
              have hi :
                  Fin.cast (honest_split_eq (n := n) i).symm k
                    =
                  Fin.natAdd i.val (0 : Fin (honest_num_open_vars (n := n) i + 1)) := by
                apply cast_split_eq_succ_last (n := n) i hlt k
                simpa [hj] using hk
              simp [addCasesFun, hi, openI, openJ]
          | cast t0 =>
              have hi :
                  Fin.cast (honest_split_eq (n := n) i).symm k
                    =
                  Fin.castAdd (honest_num_open_vars (n := n) i + 1) t0 := by
                apply cast_split_eq_succ_castSucc (n := n) i hlt k t0
                simpa [hj] using hk
              simp [addCasesFun, hi, openI, openJ]
      | right t =>
          have hi :
              Fin.cast (honest_split_eq (n := n) i).symm k
                =
              Fin.natAdd i.val (Fin.cast hm1 (Fin.succ t)) := by
            apply
              cast_split_eq_succ_right (n := n) i hlt k t
                (hm1 := by
                  simpa [openI, openJ] using hm1)
            simpa [hj] using hk
          simp [addCasesFun, hi, openI, openJ, Fin.cons, Fin.cases]

    simpa [addCasesFun] using congrArg (fun f => CPoly.CMvPolynomial.eval f p) hpoint

  -- Rewrite the two RHS branches; the goal becomes reflexive.
  rw [hbranch0, hbranch1]

lemma honest_last_round
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [DecidableEq 𝔽] [Fintype 𝔽]
  [BEq 𝔽] [LawfulBEq 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽) (r : Fin n → 𝔽) (i : Fin n)
  (hlast : i.val.succ = n) :
  next_claim (𝔽 := 𝔽) (round_challenge := r i)
      (honest_round_poly (p := p) (ch := r) i)
    =
  CPoly.CMvPolynomial.eval r p := by
  classical

  have hi : i.val + 1 = n := by
    simpa [Nat.succ_eq_add_one] using hlast

  have hopen : honest_num_open_vars (n := n) i = 0 := by
    simp [honest_num_open_vars, hi]

  -- define b0 at the dependent type via simp [hopen]
  let b0 : Fin (honest_num_open_vars (n := n) i) → 𝔽 :=
    empty_open_assignment (𝔽 := 𝔽) (n := n) i hopen

  -- last round => honest_round_poly is just F applied to the empty assignment
  have hround :
      honest_round_poly (p := p) (ch := r) i
        =
      CPoly.eval₂Poly (𝔽 := 𝔽) (n := n) c1
        (honest_combined_map (𝔽 := 𝔽) (n := n) i (challenge_subset r i) b0)
        p := by
    -- unfold to the hypercube sum
    simp [honest_round_poly, honest_prover_message_at_def]

    -- name the function being summed
    let F :
        (Fin (honest_num_open_vars (n := n) i) → 𝔽) → CPoly.CMvPolynomial 1 𝔽 :=
      fun b =>
        CPoly.eval₂Poly (𝔽 := 𝔽) (n := n) c1
          (honest_combined_map (𝔽 := 𝔽) (n := n) i (challenge_subset r i) b) p

    -- rewrite the goal *into* the shape the helper lemma produces, without `change`
    -- crucial: keep the same `add` that simp produced (it's the CMvPolynomial instHAdd one)
    -- so we use `by` + `simpa [F]` to replace the anonymous function with `F`.
    have hcollapse :=
      sum_over_hypercube_recursive_eq_of_m_eq_zero
        (𝔽 := 𝔽) (β := CPoly.CMvPolynomial 1 𝔽)
        (b0 := (0 : 𝔽)) (b1 := (1 : 𝔽))
        (add := fun a b =>
          @HAdd.hAdd (CPoly.CMvPolynomial 1 𝔽) (CPoly.CMvPolynomial 1 𝔽)
            (CPoly.CMvPolynomial 1 𝔽) instHAdd a b)
        (m := honest_num_open_vars (n := n) i) (F := F) hopen

    -- now `hcollapse` is exactly: sum_over... F = F (ndrec empty)
    -- and your `b0` is exactly that transported empty function by definition.
    simpa [F, b0, empty_open_assignment] using hcollapse

  -- expand next_claim, rewrite by hround
  have hnc :
      next_claim (𝔽 := 𝔽) (round_challenge := r i)
          (honest_round_poly (p := p) (ch := r) i)
        =
      CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
        (RingHom.id 𝔽) (fun _ : Fin 1 => r i)
        (CPoly.eval₂Poly (𝔽 := 𝔽) (n := n) c1
          (honest_combined_map (𝔽 := 𝔽) (n := n) i (challenge_subset r i) b0) p) := by
    simp [next_claim, hround]

  have heval :
      CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
        (RingHom.id 𝔽) (fun _ : Fin 1 => r i)
        (CPoly.eval₂Poly (𝔽 := 𝔽) (n := n) c1
          (honest_combined_map (𝔽 := 𝔽) (n := n) i (challenge_subset r i) b0) p)
        =
      CPoly.CMvPolynomial.eval
        (fun j =>
          CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
            (RingHom.id 𝔽) (fun _ : Fin 1 => r i)
            (honest_combined_map (𝔽 := 𝔽) (n := n) i (challenge_subset r i) b0 j))
        p := by
    simpa using
      (CPoly.eval₂_eval₂Poly_c1 (𝔽 := 𝔽) (n := n) (p := p)
        (vs := honest_combined_map (𝔽 := 𝔽) (n := n) i (challenge_subset r i) b0)
        (b := r i))

  have hpt :
      (fun j =>
        CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
          (RingHom.id 𝔽) (fun _ : Fin 1 => r i)
          (honest_combined_map (𝔽 := 𝔽) (n := n) i (challenge_subset r i) b0 j))
      =
      r := by
    funext j
    by_cases hj : j = i
    · subst hj
      -- key: combined_map at i is x0, and eval₂_x0 computes it
      have hcm :
          honest_combined_map (𝔽 := 𝔽) (n := n) j (challenge_subset r j) b0 j = x0 := by
        simpa using
          (honest_combined_map_at_i_is_x0 (𝔽 := 𝔽) (n := n)
            (i := j) (challenges := challenge_subset r j) (b := b0))

      -- now eval₂ of x0 at r j is r j
      simpa [hcm, x0] using (CPoly.eval₂_x0 (𝔽 := 𝔽) (b := r j))
    ·
      -- j ≠ i, with i last => j.val < i.val
      have hjlt_succ : j.val < i.val.succ := by
        -- j.isLt : j.val < n
        -- hlast : i.val.succ = n  so  hlast.symm : n = i.val.succ
        exact (hlast.symm ▸ j.isLt)


      have hjle : j.val ≤ i.val := Nat.le_of_lt_succ hjlt_succ
      have hne : j.val ≠ i.val := by
        intro hEq
        apply hj
        ext
        exact hEq
      have hjlt : j.val < i.val := Nat.lt_of_le_of_ne hjle hne

      let t : Fin i.val := ⟨j.val, hjlt⟩

      -- cast the left index back to Fin n
      let j' : Fin n :=
        Fin.cast (honest_split_eq (n := n) i)
          (Fin.castAdd (honest_num_open_vars (n := n) i + 1) t)

      have hj' : j' = j := by
        ext
        simp [j', t]

      have hmap' :
          honest_combined_map (𝔽 := 𝔽) (n := n) i (challenge_subset r i) b0 j'
            =
          c1 (challenge_subset r i t) := by
        simpa [j'] using
          (honest_combined_map_left (𝔽 := 𝔽) (n := n)
            (i := i) (challenges := challenge_subset r i) (b := b0) (t := t))

      have hmap :
          honest_combined_map (𝔽 := 𝔽) (n := n) i (challenge_subset r i) b0 j
            =
          c1 (challenge_subset r i t) := by
        simpa [hj'] using hmap'

      have hc :
          CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
            (RingHom.id 𝔽) (fun _ : Fin 1 => r i)
            (c1 (challenge_subset r i t))
          =
          challenge_subset r i t := by
        simp

      have htj :
          (⟨t.val, Nat.lt_trans t.isLt i.isLt⟩ : Fin n) = j := by
        ext
        rfl

      simp [hmap, challenge_subset, htj]

  -- final assembly
  calc
    next_claim (𝔽 := 𝔽) (round_challenge := r i)
        (honest_round_poly (p := p) (ch := r) i)
        =
      CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
        (RingHom.id 𝔽) (fun _ : Fin 1 => r i)
        (CPoly.eval₂Poly (𝔽 := 𝔽) (n := n) c1
          (honest_combined_map (𝔽 := 𝔽) (n := n) i (challenge_subset r i) b0) p) := by
          exact hnc
    _ =
      CPoly.CMvPolynomial.eval
        (fun j =>
          CPoly.CMvPolynomial.eval₂ (n := 1) (R := 𝔽) (S := 𝔽)
            (RingHom.id 𝔽) (fun _ : Fin 1 => r i)
            (honest_combined_map (𝔽 := 𝔽) (n := n) i (challenge_subset r i) b0 j))
        p := by
          exact heval
    _ =
      CPoly.CMvPolynomial.eval r p := by
          simp [hpt]
