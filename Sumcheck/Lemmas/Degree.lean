import CompPoly.CMvPolynomial
import CompPoly.MvPolyEquiv

import Sumcheck.Src.CMvPolynomial
import Sumcheck.Src.Hypercube
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
  simpa [residual_sum_with_openVars] using hswap.trans (by rfl)


lemma honest_prover_message_at_sum_zero_one
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽)
  (i : Fin n)
  (ch : Fin i.val → 𝔽) :
  let g := honest_prover_message_at (𝔽 := 𝔽) p i ch
  CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (0 : 𝔽)) g +
      CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (1 : 𝔽)) g
    =
    residual_sum (𝔽 := 𝔽) (k := i.val) (num_vars := n) ch p (Nat.le_of_lt i.isLt) := by
  classical
  dsimp

  -- Pin the numeric facts once (this avoids ⋯ casts drifting later)
  have hk : i.val ≤ n := Nat.le_of_lt i.isLt

  let openVars : ℕ := n - i.val
  have hn : i.val + openVars = n := by
    simpa [openVars] using Nat.add_sub_of_le hk

  -- Rewrite residual_sum into the "with_openVars" form (so hn is explicit)
  have hres :
      residual_sum (𝔽 := 𝔽) (k := i.val) (num_vars := n) ch p hk
        =
      residual_sum_with_openVars (𝔽 := 𝔽) (k := i.val) (n := n)
        (openVars := openVars) (hn := hn) ch p := by
    simpa [openVars, hn] using
      (residual_sum_eq_with_openVars_def (𝔽 := 𝔽) (k := i.val) (n := n) ch p hk)

  -- Unfold RHS into a single hypercube sum with a concrete cast proof `hn`
  -- This is the exact RHS we want to split into the 0/1 branches.
  -- (Keeping it as a `let` keeps simp from expanding too eagerly.)
  have hsplit : i.val + (honest_num_open_vars (n := n) i + 1) = n :=
    honest_split_eq (n := n) i

  -- first rewrite openVars to the “honest” one, *then* swap the hn proof used in Fin.cast:
  have hRHS_def_fixed :
      residual_sum_with_openVars (𝔽 := 𝔽) (k := i.val) (n := n)
        (openVars := openVars) (hn := hn) ch p
      =
      sum_over_hypercube_recursive (𝔽 := 𝔽) (β := 𝔽)
        (0 : 𝔽) (1 : 𝔽) (· + ·) (m := openVars)
        (fun x =>
          CPoly.CMvPolynomial.eval
            (fun j => addCasesFun ch x (Fin.cast hsplit.symm j)) p) := by
    -- this is exactly the lemma above:
    simpa using
      (residual_sum_with_openVars_def_with_hn (𝔽 := 𝔽)
        (k := i.val) (n := n) (openVars := openVars)
        (hn := hn) (hn' := hsplit) (ch := ch) (p := p))

  -- Now identify openVars = (honest_num_open_vars i).succ.
  have hopenVars :
      openVars = (honest_num_open_vars (n := n) i).succ := by
    -- prove by left-cancelling i.val from the equalities to n
    apply Nat.add_left_cancel
    -- goal: i.val + openVars = i.val + (honest_num_open_vars i).succ
    -- left side is hn
    -- right side is honest_split_eq, rewritten
    calc
      i.val + openVars = n := hn
      _ = i.val + (honest_num_open_vars (n := n) i + 1) := by
            -- honest_split_eq is: i.val + (honest_num_open_vars i + 1) = n
            simpa using (honest_split_eq (n := n) i).symm
      _ = i.val + (honest_num_open_vars (n := n) i).succ := by
            simp [Nat.succ_eq_add_one]

  -- Split the hypercube sum at the first coordinate (0/1).
  have hsplitHy :
      (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := 𝔽)
          0 1 (fun x1 x2 => x1 + x2) (m := openVars)
          (fun x =>
            CPoly.CMvPolynomial.eval
              (fun j => addCasesFun ch x (Fin.cast hn.symm j)) p))
        =
      (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := 𝔽)
          0 1 (fun x1 x2 => x1 + x2) (m := honest_num_open_vars (n := n) i)
          (fun x =>
            CPoly.CMvPolynomial.eval
              (fun j => addCasesFun ch (Fin.cons (0 : 𝔽) x) (Fin.cast hn.symm j)) p))
        +
      (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := 𝔽)
          0 1 (fun x1 x2 => x1 + x2) (m := honest_num_open_vars (n := n) i)
          (fun x =>
            CPoly.CMvPolynomial.eval
              (fun j => addCasesFun ch (Fin.cons (1 : 𝔽) x) (Fin.cast hn.symm j)) p)) := by
    -- Use the succ-splitting lemma, but we must rewrite m=openVars into succ(...)
    -- and then `simpa`.
    -- Your succ lemma is definitional, so `simp [hopenVars]` is enough.
    simpa [hopenVars] using
      (sum_over_hypercube_recursive_succ (𝔽 := 𝔽) (β := 𝔽)
        (b0 := (0 : 𝔽)) (b1 := (1 : 𝔽)) (add := (fun x1 x2 => x1 + x2))
        (m := honest_num_open_vars (n := n) i)
        (F := fun x =>
          CPoly.CMvPolynomial.eval (fun j => addCasesFun ch x (Fin.cast hn.symm j)) p))

  -- *** THIS IS THE FIX FOR YOUR RW FAILURE ***
  -- Your goal’s RHS is written using `Fin.addCases`, but hsplitHy uses `addCasesFun`.
  -- Normalize *once* so `rw` works later.
  have hsplitHy_fin :
      (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := 𝔽)
          0 1 (fun x1 x2 => x1 + x2) (m := openVars)
          (fun x =>
            CPoly.CMvPolynomial.eval
              (fun j => Fin.addCases ch x (Fin.cast hn.symm j)) p))
        =
      (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := 𝔽)
          0 1 (fun x1 x2 => x1 + x2) (m := honest_num_open_vars (n := n) i)
          (fun x =>
            CPoly.CMvPolynomial.eval
              (fun j => Fin.addCases ch (Fin.cons (0 : 𝔽) x) (Fin.cast hn.symm j)) p))
        +
      (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := 𝔽)
          0 1 (fun x1 x2 => x1 + x2) (m := honest_num_open_vars (n := n) i)
          (fun x =>
            CPoly.CMvPolynomial.eval
              (fun j => Fin.addCases ch (Fin.cons (1 : 𝔽) x) (Fin.cast hn.symm j)) p)) := by
    simpa [addCasesFun] using hsplitHy

  -- From here, the structure is:
  --
  -- 1) rewrite RHS using hres + hRHS_def and then hsplitHy_fin
  -- 2) show eval₂ at 0 of honest_prover_message_at = left branch
  -- 3) show eval₂ at 1 of honest_prover_message_at = right branch
  --
  -- Those last two use your “eval₂ commutes with eval₂Poly/substitution” lemma(s).

  -- Step 1: rewrite the RHS into the split form.
  -- (We do it as a calc so there’s no brittle `rw` pattern-matching.)
  have hRHS_split :
      residual_sum (𝔽 := 𝔽) (k := i.val) (num_vars := n) ch p hk
        =
      (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := 𝔽)
          0 1 (fun x1 x2 => x1 + x2) (m := honest_num_open_vars (n := n) i)
          (fun x =>
            CPoly.CMvPolynomial.eval
              (fun j => Fin.addCases ch (Fin.cons (0 : 𝔽) x) (Fin.cast hn.symm j)) p))
        +
      (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := 𝔽)
          0 1 (fun x1 x2 => x1 + x2) (m := honest_num_open_vars (n := n) i)
          (fun x =>
            CPoly.CMvPolynomial.eval
              (fun j => Fin.addCases ch (Fin.cons (1 : 𝔽) x) (Fin.cast hn.symm j)) p)) := by
    -- expand residual_sum via hres + hRHS_def, then apply the split lemma
    calc
      residual_sum (𝔽 := 𝔽) (k := i.val) (num_vars := n) ch p hk
          =
        residual_sum_with_openVars (𝔽 := 𝔽) (k := i.val) (n := n)
          (openVars := openVars) (hn := hn) ch p := hres
      _ =
        sum_over_hypercube_recursive (𝔽 := 𝔽) (β := 𝔽)
          0 1 (fun x1 x2 => x1 + x2) (m := openVars)
          (fun x =>
            CPoly.CMvPolynomial.eval
              (fun j => addCasesFun ch x (Fin.cast hn.symm j)) p) := hRHS_def
      _ =
        sum_over_hypercube_recursive (𝔽 := 𝔽) (β := 𝔽)
          0 1 (fun x1 x2 => x1 + x2) (m := openVars)
          (fun x =>
            CPoly.CMvPolynomial.eval
              (fun j => Fin.addCases ch x (Fin.cast hn.symm j)) p) := by
            simp [addCasesFun]
      _ =
        (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := 𝔽)
            0 1 (fun x1 x2 => x1 + x2) (m := honest_num_open_vars (n := n) i)
            (fun x =>
              CPoly.CMvPolynomial.eval
                (fun j => Fin.addCases ch (Fin.cons (0 : 𝔽) x) (Fin.cast hn.symm j)) p))
          +
        (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := 𝔽)
            0 1 (fun x1 x2 => x1 + x2) (m := honest_num_open_vars (n := n) i)
            (fun x =>
              CPoly.CMvPolynomial.eval
                (fun j => Fin.addCases ch (Fin.cons (1 : 𝔽) x) (Fin.cast hn.symm j)) p)) := by
            exact hsplitHy_fin

  -- Step 2+3: reduce the main goal to those two “eval₂ of honest message = branch” facts.
  -- Replace the goal RHS using hRHS_split, then split.
  -- (This is exactly where your commutation lemma(s) plug in.)
  --
  -- NOTE: you should replace `*_COMMUTES_*` with the actual lemma you have in your repo.
  --
  -- Example shape you want:
  --   eval₂ id (fun _ => b) (honest_prover_message_at p i ch)
  --     = sum_over_hypercube_recursive ... (fun x => eval (point with current=b and rest=x) p)
  --
  -- Once you have those two lemmas, the finish is just `simp [hRHS_split, ...]`.
  --
  -- I’ll leave the exact invocations to your existing lemma names.
  --
  -- Final:
  --   simpa [hRHS_split] using congrArg (fun t => ? ) ...
  --
  -- For now we finish by rewriting the goal with hRHS_split and leaving the two obligations explicit:

  -- rewrite goal RHS:
  have : (CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (0 : 𝔽))
            (honest_prover_message_at (𝔽 := 𝔽) p i ch))
        +
        (CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => (1 : 𝔽))
            (honest_prover_message_at (𝔽 := 𝔽) p i ch))
        =
        (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := 𝔽)
            0 1 (fun x1 x2 => x1 + x2) (m := honest_num_open_vars (n := n) i)
            (fun x =>
              CPoly.CMvPolynomial.eval
                (fun j => Fin.addCases ch (Fin.cons (0 : 𝔽) x) (Fin.cast hn.symm j)) p))
          +
        (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := 𝔽)
            0 1 (fun x1 x2 => x1 + x2) (m := honest_num_open_vars (n := n) i)
            (fun x =>
              CPoly.CMvPolynomial.eval
                (fun j => Fin.addCases ch (Fin.cons (1 : 𝔽) x) (Fin.cast hn.symm j)) p)) := by
    -- This is exactly where you apply your two commutation lemmas.
    --
    -- Replace the next two `have`s with your actual lemma names:
    --
    -- have h0 : eval₂ ...0 (honest_prover_message_at ...) = left_branch := by ...
    -- have h1 : eval₂ ...1 (honest_prover_message_at ...) = right_branch := by ...
    --
    -- and then:
    -- simpa [h0, h1]
    --
    -- Since I don't have those lemma names in the pasted context, I can't write them
    -- without guessing and breaking your file.
    --
    -- So: stop here in your file, and plug in h0/h1.
    --
    admit

  -- now finish using hRHS_split
  -- (after you replace the admit above, this closes)
  -- NOTE: `this` is the split-form LHS, hRHS_split is the split-form RHS.
  -- Just chain them.
  simpa [hRHS_split] using this
