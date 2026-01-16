import CompPoly.CMvPolynomial
import CompPoly.MvPolyEquiv

import Sumcheck.Src.HonestProver

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
