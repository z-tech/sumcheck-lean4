import CompPoly.CMvPolynomial
import CompPoly.MvPolyEquiv

import Sumcheck.Src.CMvPolynomial
import Sumcheck.Src.HonestProver
import Sumcheck.Src.HonestTranscript

import Sumcheck.Lemmas.Hypercube
import Sumcheck.Lemmas.CMvPolynomial
import Sumcheck.Lemmas.HonestProverCore

noncomputable def deg1
  {𝔽 : Type _} [CommSemiring 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (q : CPoly.CMvPolynomial 1 𝔽) : ℕ :=
  (CPoly.fromCMvPolynomial q).degreeOf (⟨0, by decide⟩ : Fin 1)

@[simp] lemma fromCMvPolynomial_add
  {𝔽 : Type _} [CommSemiring 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  {n : ℕ} (p q : CPoly.CMvPolynomial n 𝔽) :
  CPoly.fromCMvPolynomial (R := 𝔽) (p + q) = CPoly.fromCMvPolynomial (R := 𝔽) p + CPoly.fromCMvPolynomial (R := 𝔽) q := by
  classical
  ext s
  -- unfold *just enough* that coeff is `toFun`
  simp [CPoly.fromCMvPolynomial, MvPolynomial.coeff]
  -- if there is still a goal, it should now be literally `rfl` or a `simp` ring goal
  rfl

lemma degreeOf_add_le_of_le
  {𝔽 : Type _} [CommSemiring 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (d : ℕ)
  (a b : CPoly.CMvPolynomial 1 𝔽)
  (ha : CPoly.CMvPolynomial.degreeOf (0 : Fin 1) a ≤ d)
  (hb : CPoly.CMvPolynomial.degreeOf (0 : Fin 1) b ≤ d) :
  CPoly.CMvPolynomial.degreeOf (0 : Fin 1) (a + b) ≤ d := by
  classical
  let i0 : Fin 1 := 0
  let A : MvPolynomial (Fin 1) 𝔽 := CPoly.fromCMvPolynomial (R := 𝔽) a
  let B : MvPolynomial (Fin 1) 𝔽 := CPoly.fromCMvPolynomial (R := 𝔽) b

  -- CPoly degreeOf = MvPolynomial degreeOf (at i0)
  have hEqA :
      CPoly.CMvPolynomial.degreeOf i0 a
        = MvPolynomial.degreeOf (σ := Fin 1) (R := 𝔽) i0 A := by
    -- degreeOf_equiv : (degreeOf on CMvPolynomial) = (degreeOf on fromCMvPolynomial) as functions
    simpa [A] using congrArg (fun f => f i0) (CPoly.degreeOf_equiv (p := a) (S := 𝔽))

  have hEqB :
      CPoly.CMvPolynomial.degreeOf i0 b
        = MvPolynomial.degreeOf (σ := Fin 1) (R := 𝔽) i0 B := by
    simpa [B] using congrArg (fun f => f i0) (CPoly.degreeOf_equiv (p := b) (S := 𝔽))

  have ha' : MvPolynomial.degreeOf (σ := Fin 1) (R := 𝔽) i0 A ≤ d := by
    simpa [i0, hEqA] using ha

  have hb' : MvPolynomial.degreeOf (σ := Fin 1) (R := 𝔽) i0 B ≤ d := by
    simpa [i0, hEqB] using hb

  have hEqAB :
      CPoly.CMvPolynomial.degreeOf i0 (a + b)
        = MvPolynomial.degreeOf (σ := Fin 1) (R := 𝔽) i0 (CPoly.fromCMvPolynomial (R := 𝔽) (a + b)) := by
    simpa using congrArg (fun f => f i0) (CPoly.degreeOf_equiv (p := a + b) (S := 𝔽))

  -- Use Mathlib: degreeOf i0 (A+B) ≤ max (degreeOf i0 A) (degreeOf i0 B)
  have hMvAdd :
      MvPolynomial.degreeOf (σ := Fin 1) (R := 𝔽) i0 (A + B)
        ≤
      max (MvPolynomial.degreeOf (σ := Fin 1) (R := 𝔽) i0 A)
          (MvPolynomial.degreeOf (σ := Fin 1) (R := 𝔽) i0 B) :=
    MvPolynomial.degreeOf_add_le (R := 𝔽) (σ := Fin 1) i0 A B

  have hMax : max
      (MvPolynomial.degreeOf (σ := Fin 1) (R := 𝔽) i0 A)
      (MvPolynomial.degreeOf (σ := Fin 1) (R := 𝔽) i0 B) ≤ d :=
    max_le_iff.mpr ⟨ha', hb'⟩

  -- rewrite fromCMvPolynomial (a+b) to A+B, then transfer back
  have hMv :
      MvPolynomial.degreeOf (σ := Fin 1) (R := 𝔽) i0 (CPoly.fromCMvPolynomial (R := 𝔽) (a + b)) ≤ d := by
    -- fromCMvPolynomial (a+b) = A + B
    -- and A,B are defs above
    simpa [A, B, fromCMvPolynomial_add (𝔽 := 𝔽) (p := a) (q := b)] using
      le_trans hMvAdd hMax

  -- convert back to CPoly
  have : CPoly.CMvPolynomial.degreeOf i0 (a + b) ≤ d := by
    simpa [hEqAB] using hMv

  simpa [i0] using this

lemma hadd_degreeOf0_le
  {𝔽 : Type _} [CommSemiring 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (d : ℕ) :
  ∀ a b : CPoly.CMvPolynomial 1 𝔽,
    CPoly.CMvPolynomial.degreeOf (0 : Fin 1) a ≤ d →
    CPoly.CMvPolynomial.degreeOf (0 : Fin 1) b ≤ d →
    CPoly.CMvPolynomial.degreeOf (0 : Fin 1) (Add.add a b) ≤ d := by
  intro a b ha hb
  -- Don't simp; just change the goal to the usual (a + b) form and apply your lemma.
  -- This avoids whnf expanding Add/HAdd.
  change CPoly.CMvPolynomial.degreeOf (0 : Fin 1) (a + b) ≤ d
  exact degreeOf_add_le_of_le (𝔽 := 𝔽) (d := d) a b ha hb


set_option maxHeartbeats 90000000 in
lemma degree_honest_prover_message_at_le_of_per_b
  {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  {n : ℕ}
  (p : CPoly.CMvPolynomial n 𝔽)
  (i : Fin n)
  (challenges : Fin i.val → 𝔽)
  (d : ℕ)
  (hF :
    ∀ b : Fin (honest_num_open_vars (n := n) i) → 𝔽,
      CPoly.CMvPolynomial.degreeOf (0 : Fin 1)
        (CPoly.eval₂Poly c1 (honest_combined_map (𝔽 := 𝔽) (n := n) i challenges b) p)
      ≤ d) :
  CPoly.CMvPolynomial.degreeOf (0 : Fin 1)
      (honest_prover_message_at (𝔽 := 𝔽) (p := p) (i := i) (challenges := challenges))
    ≤ d := by
  classical

  -- degree functional
  let deg : CPoly.CMvPolynomial 1 𝔽 → ℕ :=
    fun q => CPoly.CMvPolynomial.degreeOf (0 : Fin 1) q

  -- CRITICAL: choose the *homogeneous* HAdd instance explicitly.
  -- This prevents Lean from using Lawful.instHAddMaxNat.
  let add1 :
      CPoly.CMvPolynomial 1 𝔽 → CPoly.CMvPolynomial 1 𝔽 → CPoly.CMvPolynomial 1 𝔽 :=
    fun a b =>
      @HAdd.hAdd
        (CPoly.CMvPolynomial 1 𝔽) (CPoly.CMvPolynomial 1 𝔽) (CPoly.CMvPolynomial 1 𝔽)
        instHAdd a b

  have hadd :
      ∀ a b : CPoly.CMvPolynomial 1 𝔽,
        deg a ≤ d →
        deg b ≤ d →
        deg (add1 a b) ≤ d := by
    intro a b ha hb
    dsimp [deg, add1] at ha hb ⊢
    -- goal is now exactly the shape produced by degreeOf_add_le_of_le
    exact degreeOf_add_le_of_le (𝔽 := 𝔽) (d := d) a b ha hb

  have h :=
    sum_over_hypercube_recursive_deg_le
      (𝔽 := 𝔽)
      (β := CPoly.CMvPolynomial 1 𝔽)
      (deg := deg)
      (d := d)
      (b0 := (0 : 𝔽)) (b1 := (1 : 𝔽))
      (add := add1)
      (m := honest_num_open_vars (n := n) i)
      (F := fun b =>
        CPoly.eval₂Poly c1 (honest_combined_map (𝔽 := 𝔽) (n := n) i challenges b) p)
      (hadd := hadd)
      (hF := hF)

  -- Finish by unfolding honest_prover_message_at, then aligning `add` with `add1`.
  -- NOTE: this last step will work *iff* honest_prover_message_at uses the homogeneous add.
  -- If your honest_prover_message_at currently uses `fun a b => a + b`, I recommend changing it
  -- to exactly `add1` (or to the typed version of +) as shown below.
  simpa [honest_prover_message_at, deg, add1] using h

lemma residual_sum_with_openVars_cast_congr
  {𝔽 : Type _} [CommRing 𝔽] [DecidableEq 𝔽]
  {k n openVars : ℕ}
  (hn₁ hn₂ : k + openVars = n)
  (ch : Fin k → 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽) :
  residual_sum_with_openVars (𝔽 := 𝔽) (k := k) (n := n)
      (openVars := openVars) (hn := hn₁) ch p
    =
  residual_sum_with_openVars (𝔽 := 𝔽) (k := k) (n := n)
      (openVars := openVars) (hn := hn₂) ch p := by
  classical
  -- `residual_sum_with_openVars` differs only in the `Fin.cast hn.symm` proof.
  -- Proofs of equalities live in Prop, so they are subsingletons.
  have hhn : hn₁ = hn₂ := Subsingleton.elim _ _
  subst hhn
  rfl


lemma residual_sum_with_openVars_def_with_hn
  {𝔽 : Type _} [CommRing 𝔽] [DecidableEq 𝔽]
  {k n openVars : ℕ}
  (hn hn' : k + openVars = n)
  (ch : Fin k → 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽) :
  residual_sum_with_openVars (𝔽 := 𝔽) (k := k) (n := n)
      (openVars := openVars) (hn := hn) ch p
    =
  sum_over_hypercube_recursive (𝔽 := 𝔽) (β := 𝔽)
      (0 : 𝔽) (1 : 𝔽) (· + ·) (m := openVars)
      (fun x =>
        let point : Fin n → 𝔽 :=
          fun j => addCasesFun ch x (Fin.cast hn'.symm j)
        CPoly.CMvPolynomial.eval point p) := by
  classical
  -- Start from the definitional RHS (which uses hn),
  -- then swap hn -> hn' using proof-irrelevance.
  have hswap :
      residual_sum_with_openVars (𝔽 := 𝔽) (k := k) (n := n)
          (openVars := openVars) (hn := hn) ch p
        =
      residual_sum_with_openVars (𝔽 := 𝔽) (k := k) (n := n)
          (openVars := openVars) (hn := hn') ch p :=
    residual_sum_with_openVars_cast_congr (𝔽 := 𝔽) (k := k) (n := n)
      (openVars := openVars) hn hn' ch p

  -- Now unfold the definition on the hn' side.
  -- (This produces exactly the `Fin.cast hn'.symm` you want.)
  simp [residual_sum_with_openVars]

theorem degreeOf_x0_le_one {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽] :
  CPoly.CMvPolynomial.degreeOf (0 : Fin 1) (x0 (𝔽 := 𝔽)) ≤ 1 := by
  classical
  -- sanity check: our helper axiom works
  have hx :
      CPoly.fromCMvPolynomial (R := 𝔽) (x0 (𝔽 := 𝔽))
        = (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) 𝔽) := by
    simpa using (fromCMvPolynomial_x0_eq_X (𝔽 := 𝔽))

  -- now translate CPoly.degreeOf to MvPolynomial.degreeOf
  let i0 : Fin 1 := 0
  have hEq :
      CPoly.CMvPolynomial.degreeOf i0 (x0 (𝔽 := 𝔽))
        =
      MvPolynomial.degreeOf (σ := Fin 1) (R := 𝔽) i0
        (CPoly.fromCMvPolynomial (R := 𝔽) (x0 (𝔽 := 𝔽))) := by
    simpa using
      congrArg (fun f => f i0) (CPoly.degreeOf_equiv (p := (x0 (𝔽 := 𝔽))) (S := 𝔽))

  have h : CPoly.CMvPolynomial.degreeOf i0 (x0 (𝔽 := 𝔽)) ≤ 1 := by
    rw [hEq]
    -- use the explicit rewrite first, then compute degree
    rw [hx]
    simp [MvPolynomial.degreeOf_X, i0]

  simpa [i0] using h

theorem degreeOf_mul_le_univariate {𝔽 : Type _} [CommSemiring 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
(a b : CPoly.CMvPolynomial 1 𝔽) :
  CPoly.CMvPolynomial.degreeOf (0 : Fin 1) (Mul.mul a b)
    ≤ CPoly.CMvPolynomial.degreeOf (0 : Fin 1) a + CPoly.CMvPolynomial.degreeOf (0 : Fin 1) b := by
  classical
  let i0 : Fin 1 := 0
  let A : MvPolynomial (Fin 1) 𝔽 := CPoly.fromCMvPolynomial (R := 𝔽) a
  let B : MvPolynomial (Fin 1) 𝔽 := CPoly.fromCMvPolynomial (R := 𝔽) b

  -- CPoly degreeOf = MvPolynomial degreeOf (at i0)
  have hEqA :
      CPoly.CMvPolynomial.degreeOf i0 a
        = MvPolynomial.degreeOf (σ := Fin 1) (R := 𝔽) i0 A := by
    simpa [A] using congrArg (fun f => f i0) (CPoly.degreeOf_equiv (p := a) (S := 𝔽))

  have hEqB :
      CPoly.CMvPolynomial.degreeOf i0 b
        = MvPolynomial.degreeOf (σ := Fin 1) (R := 𝔽) i0 B := by
    simpa [B] using congrArg (fun f => f i0) (CPoly.degreeOf_equiv (p := b) (S := 𝔽))

  have hEqAB :
      CPoly.CMvPolynomial.degreeOf i0 (Mul.mul a b)
        =
      MvPolynomial.degreeOf (σ := Fin 1) (R := 𝔽) i0 (CPoly.fromCMvPolynomial (R := 𝔽) (Mul.mul a b)) := by
    simpa using congrArg (fun f => f i0) (CPoly.degreeOf_equiv (p := Mul.mul a b) (S := 𝔽))

  -- Rewrite `fromCMvPolynomial (Mul.mul a b)` as `A * B`
  have hmap :
      CPoly.fromCMvPolynomial (R := 𝔽) (Mul.mul a b) = A * B := by
    -- Avoid `simp` here: `CPoly.map_mul` is itself a simp lemma and `simpa` would reduce to `True`.
    dsimp [A, B]
    change
      CPoly.fromCMvPolynomial (R := 𝔽) (a * b) =
        CPoly.fromCMvPolynomial (R := 𝔽) a * CPoly.fromCMvPolynomial (R := 𝔽) b
    exact CPoly.map_mul (a := a) (b := b) (R := 𝔽)

  -- Main MvPolynomial inequality
  have hMv :
      MvPolynomial.degreeOf (σ := Fin 1) (R := 𝔽) i0 (CPoly.fromCMvPolynomial (R := 𝔽) (Mul.mul a b))
        ≤
      MvPolynomial.degreeOf (σ := Fin 1) (R := 𝔽) i0 A + MvPolynomial.degreeOf (σ := Fin 1) (R := 𝔽) i0 B := by
    -- apply Mathlib on `A * B`, then rewrite by `hmap`
    -- `hmap` is oriented `from = A*B`, so we rewrite in the reverse direction.
    simpa [hmap] using
      (MvPolynomial.degreeOf_mul_le (R := 𝔽) (σ := Fin 1) i0 A B)

  -- transfer back to CPoly
  have : CPoly.CMvPolynomial.degreeOf i0 (Mul.mul a b)
      ≤ CPoly.CMvPolynomial.degreeOf i0 a + CPoly.CMvPolynomial.degreeOf i0 b := by
    simpa [hEqAB, hEqA, hEqB] using hMv

  simpa [i0] using this

theorem degreeOf_c1_eq_zero {𝔽 : Type _} [CommSemiring 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
(c : 𝔽) :
  CPoly.CMvPolynomial.degreeOf (0 : Fin 1) (c1 (𝔽 := 𝔽) c) = 0 := by
  classical
  let i0 : Fin 1 := 0

  -- Bridge `CPoly.CMvPolynomial.degreeOf` to `MvPolynomial.degreeOf`.
  have hEq :
      CPoly.CMvPolynomial.degreeOf i0 (c1 (𝔽 := 𝔽) c)
        = MvPolynomial.degreeOf (σ := Fin 1) (R := 𝔽) i0
            (CPoly.fromCMvPolynomial (R := 𝔽) (c1 (𝔽 := 𝔽) c)) := by
    simpa using
      congrArg (fun f => f i0)
        (CPoly.degreeOf_equiv (p := c1 (𝔽 := 𝔽) c) (S := 𝔽))

  -- Rewrite to the `MvPolynomial` side and use `MvPolynomial.degreeOf_C`.
  rw [hEq]
  rw [fromCMvPolynomial_c1_eq_C (𝔽 := 𝔽) (c := c)]
  simp [i0]

theorem degreeOf_pow_univariate_le {𝔽 : Type _} [CommRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
(q : CPoly.CMvPolynomial 1 𝔽) :
  ∀ e : ℕ,
    CPoly.CMvPolynomial.degreeOf (0 : Fin 1) (pow_univariate (𝔽 := 𝔽) q e)
      ≤ e * CPoly.CMvPolynomial.degreeOf (0 : Fin 1) q := by
  intro e
  induction e with
  | zero =>
      have h0 :
          CPoly.CMvPolynomial.degreeOf (0 : Fin 1)
              (pow_univariate (𝔽 := 𝔽) q 0) = 0 := by
        simpa [pow_univariate] using
          (degreeOf_c1_eq_zero (𝔽 := 𝔽) (c := (1 : 𝔽)))
      -- goal is an inequality, but simp turns `≤ 0` into `= 0`
      simp [h0]
  | succ e ih =>
      have hmul :=
        degreeOf_mul_le_univariate (𝔽 := 𝔽) q (pow_univariate (𝔽 := 𝔽) q e)
      have h1 :
          CPoly.CMvPolynomial.degreeOf (0 : Fin 1)
              (Mul.mul q (pow_univariate (𝔽 := 𝔽) q e))
            ≤
            CPoly.CMvPolynomial.degreeOf (0 : Fin 1) q +
              e * CPoly.CMvPolynomial.degreeOf (0 : Fin 1) q := by
        refine le_trans hmul ?_
        exact Nat.add_le_add_left ih (CPoly.CMvPolynomial.degreeOf (0 : Fin 1) q)
      have harith :
          CPoly.CMvPolynomial.degreeOf (0 : Fin 1) q +
              e * CPoly.CMvPolynomial.degreeOf (0 : Fin 1) q
            ≤
            Nat.succ e * CPoly.CMvPolynomial.degreeOf (0 : Fin 1) q := by
        -- rewrite the RHS using `succ_mul`, then commute the sum on the LHS
        -- to make it reflexive.
        simp [Nat.succ_mul, Nat.add_comm]
      have h2 := le_trans h1 harith
      simpa [pow_univariate] using h2


theorem degree_subst_monomial_honest_combined_le_exp_i {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
(r : Fin n → 𝔽) (i : Fin n)
(b : Fin (honest_num_open_vars (n := n) i) → 𝔽)
(m : CPoly.CMvMonomial n) :
  CPoly.CMvPolynomial.degreeOf (0 : Fin 1)
      (subst_monomial (n := n) (𝔽 := 𝔽)
        (honest_combined_map (𝔽 := 𝔽) (n := n) i (challenge_subset r i) b) m)
    ≤ extract_exp_var_i m i := by
  classical
  -- set up abbreviations
  let vs : Fin n → CPoly.CMvPolynomial 1 𝔽 :=
    honest_combined_map (𝔽 := 𝔽) (n := n) i (challenge_subset r i) b
  let deg : CPoly.CMvPolynomial 1 𝔽 → ℕ :=
    fun q => CPoly.CMvPolynomial.degreeOf (0 : Fin 1) q
  let term : Fin n → CPoly.CMvPolynomial 1 𝔽 :=
    fun j => pow_univariate (𝔽 := 𝔽) (vs j) (extract_exp_var_i m j)
  let degPow : Fin n → ℕ := fun j => deg (term j)

  -- bound degree of a foldl product by degree(acc) + sum of degrees
  have hfold :
      ∀ (L : List (Fin n)) (acc : CPoly.CMvPolynomial 1 𝔽),
        deg (L.foldl (fun a j => Mul.mul a (term j)) acc)
          ≤ deg acc + ((L.map degPow).sum) := by
    intro L acc
    induction L generalizing acc with
    | nil =>
        simp [deg]
    | cons j L ih =>
        have ih' := ih (acc := Mul.mul acc (term j))
        have hmul : deg (Mul.mul acc (term j)) ≤ deg acc + deg (term j) := by
          simpa [deg] using (degreeOf_mul_le_univariate (a := acc) (b := term j))
        have h := le_trans ih' (Nat.add_le_add_right hmul _)
        simpa [List.foldl, List.map, degPow, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

  -- specialize to subst_monomial
  have hdeg_subst_le_list :
      deg (subst_monomial (n := n) (𝔽 := 𝔽) vs m)
        ≤ ((List.finRange n).map degPow).sum := by
    have h0 : deg (c1 (𝔽 := 𝔽) (1 : 𝔽)) = 0 := by
      simpa [deg] using (degreeOf_c1_eq_zero (𝔽 := 𝔽) (c := (1 : 𝔽)))
    have h := hfold (L := List.finRange n) (acc := c1 (𝔽 := 𝔽) (1 : 𝔽))
    have h' := h
    rw [h0] at h'
    simpa [subst_monomial, term, degPow, deg] using h'

  -- rewrite list sum as a Fintype sum
  have hsum_univ : (∑ j : Fin n, degPow j) = ((List.finRange n).map degPow).sum := by
    simpa using (Fin.sum_univ_def (n := n) (f := degPow))

  have hdeg_subst_le_sum :
      deg (subst_monomial (n := n) (𝔽 := 𝔽) vs m) ≤ ∑ j : Fin n, degPow j := by
    have hsum_univ' : ((List.finRange n).map degPow).sum = ∑ j : Fin n, degPow j := by
      simpa using hsum_univ.symm
    simpa [hsum_univ'] using hdeg_subst_le_list

  -- show deg (vs j) = 0 for j ≠ i
  have hdeg_vs_other : ∀ j : Fin n, j ≠ i → deg (vs j) = 0 := by
    intro j hj
    have hdef :=
      (honest_combined_map_def (𝔽 := 𝔽) (n := n) (i := i)
        (challenges := challenge_subset r i) (b := b) (j := j))
    have hcast :
        vs j =
          Fin.addCases (m := i.val) (n := honest_num_open_vars (n := n) i + 1)
            (motive := fun _ => CPoly.CMvPolynomial 1 𝔽)
            (fun t : Fin i.val => c1 (𝔽 := 𝔽) (challenge_subset r i t))
            (honest_right_map (𝔽 := 𝔽) (n := n) i b)
            (Fin.cast (honest_split_eq (n := n) i).symm j) := by
      simpa [vs] using hdef
    rw [hcast]
    cases h : (Fin.cast (honest_split_eq (n := n) i).symm j) using Fin.addCases with
    | left t =>
        simpa [Fin.addCases, h, deg] using
          (degreeOf_c1_eq_zero (𝔽 := 𝔽) (c := challenge_subset r i t))
    | right t =>
        -- simplify the goal but keep the equation `h` around
        simp [Fin.addCases]
        cases t using Fin.cases with
        | zero =>
            exfalso
            have hjEq : j = i := by
              have := congrArg (Fin.cast (honest_split_eq (n := n) i)) h
              simpa [honest_current_index_eq (n := n) i] using this
            exact hj hjEq
        | succ t' =>
            cases t' with
            | mk tv htv =>
                simpa [deg, honest_right_map] using
                  (degreeOf_c1_eq_zero (𝔽 := 𝔽) (c := b ⟨tv, htv⟩))

  -- show degPow j = 0 for j ≠ i
  have hdegPow_other : ∀ j : Fin n, j ≠ i → degPow j = 0 := by
    intro j hj
    have hpow : degPow j ≤ (extract_exp_var_i m j) * deg (vs j) := by
      simpa [degPow, deg] using
        (degreeOf_pow_univariate_le (𝔽 := 𝔽) (q := vs j) (extract_exp_var_i m j))
    have hdeg0 : deg (vs j) = 0 := hdeg_vs_other j hj
    have : degPow j ≤ 0 := by
      simpa [hdeg0] using hpow
    exact Nat.eq_zero_of_le_zero this

  -- collapse the Fintype sum to the single i-term
  have hsum_single : (∑ j : Fin n, degPow j) = degPow i := by
    classical
    refine (Fintype.sum_eq_single (a := i) (f := degPow) ?_)
    intro j hj
    exact hdegPow_other j hj

  -- bound the i-term by the exponent
  have hdegPow_i : degPow i ≤ extract_exp_var_i m i := by
    have hxi : vs i = x0 (𝔽 := 𝔽) := by
      simpa [vs] using
        (honest_combined_map_at_i_is_x0 (𝔽 := 𝔽) (n := n) (i := i)
          (challenges := challenge_subset r i) (b := b))
    have hpow : degPow i ≤ (extract_exp_var_i m i) * deg (vs i) := by
      simpa [degPow, deg] using
        (degreeOf_pow_univariate_le (𝔽 := 𝔽) (q := vs i) (extract_exp_var_i m i))
    have hx0 : deg (vs i) ≤ 1 := by
      simpa [deg, hxi] using (degreeOf_x0_le_one (𝔽 := 𝔽))
    have hmul : (extract_exp_var_i m i) * deg (vs i) ≤ extract_exp_var_i m i := by
      simpa [Nat.mul_one] using (Nat.mul_le_mul_left (extract_exp_var_i m i) hx0)
    exact le_trans hpow hmul

  -- final assembly
  have :
      deg (subst_monomial (n := n) (𝔽 := 𝔽) vs m) ≤ extract_exp_var_i m i := by
    calc
      deg (subst_monomial (n := n) (𝔽 := 𝔽) vs m)
          ≤ ∑ j : Fin n, degPow j := hdeg_subst_le_sum
      _ = degPow i := hsum_single
      _ ≤ extract_exp_var_i m i := hdegPow_i

  simpa [degPow, deg, term, vs] using this
