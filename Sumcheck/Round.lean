import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Data.ZMod.Basic

import Mathlib.Data.Fintype.Card
import Mathlib

import CompPoly
import CompPoly.CMvPolynomial
import CompPoly.CMvMonomial
import CompPoly.Lawful

import Sumcheck.Prover
import Sumcheck.Verifier
import Sumcheck.Polynomials

-- if g != h, the number of inputs x that make g(x) = h(x) is at most deg(g - h) / |𝔽|
-- eq. probability that random challenge makes diff poly q evaluate to zero pr[(g - h)(0) = 0] = deg(g - h) / |𝔽|
lemma one_round_soundness
  {𝔽 : Type _} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (g h : CPoly.CMvPolynomial 1 𝔽)
  (hgh : g ≠ h) :
  (↑{f ∈ Fintype.piFinset (fun _ : Fin 1 => (Finset.univ : Finset 𝔽))
        | CPoly.CMvPolynomial.eval f g = CPoly.CMvPolynomial.eval f h}.card : ℚ)
    / (Fintype.card 𝔽 : ℚ)
  ≤ ((MvPolynomial.totalDegree (CPoly.fromCMvPolynomial g - CPoly.fromCMvPolynomial h) : ℕ) : ℚ)
      / (Fintype.card 𝔽 : ℚ) := by
  classical

  -- `piFinset (fun _ => univ)` is just `univ` on functions
  have hpi :
      (Fintype.piFinset (fun _ : Fin 1 => (Finset.univ : Finset 𝔽)))
        = (Finset.univ : Finset (Fin 1 → 𝔽)) := by
    ext f
    simp

  -- Nonzero on the MvPolynomial side
  have hp :
      (CPoly.fromCMvPolynomial g - CPoly.fromCMvPolynomial h)
        ≠ (0 : MvPolynomial (Fin 1) 𝔽) := by
    intro hp0
    have hfrom : CPoly.fromCMvPolynomial g = CPoly.fromCMvPolynomial h := by
      have : CPoly.fromCMvPolynomial g - CPoly.fromCMvPolynomial h = 0 := by
        simpa using hp0
      exact sub_eq_zero.mp this
    have : g = h :=
      (CPoly.eq_iff_fromCMvPolynomial (u := g) (v := h)).2 hfrom
    exact hgh this

  -- Schwartz–Zippel on the difference polynomial
  have sz :=
    MvPolynomial.schwartz_zippel_totalDegree
      (R := 𝔽)
      (p := CPoly.fromCMvPolynomial g - CPoly.fromCMvPolynomial h)
      hp
      (S := (Finset.univ : Finset 𝔽))

  -- Turn `eval(from g) - eval(from h) = 0` into `eval g = eval h`,
  -- and rewrite `univ` as your `piFinset`.
  simpa [hpi,
        CPoly.eval_equiv (p := g),
        CPoly.eval_equiv (p := h),
        sub_eq_zero,
        pow_one] using sz

@[simp] lemma verifier_expected_claim_eq_eval
  {𝔽} [CommRing 𝔽] [DecidableEq 𝔽]
  (p : CPoly.CMvPolynomial 1 𝔽) (r : 𝔽) :
  verifier_expected_claim (𝔽 := 𝔽) p r
    = CPoly.CMvPolynomial.eval (fun _ : Fin 1 => r) p := by
  simp [verifier_expected_claim, CPoly.CMvPolynomial.eval]

@[simp] lemma one_round_expected_claim_soundness
  {𝔽 : Type _} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (g h : CPoly.CMvPolynomial 1 𝔽)
  (hgh : g ≠ h) :
  (↑{r ∈ (Finset.univ : Finset 𝔽)
      | verifier_expected_claim (𝔽 := 𝔽) g r
          = verifier_expected_claim (𝔽 := 𝔽) h r}.card : ℚ)
    / (Fintype.card 𝔽 : ℚ)
  ≤ ((MvPolynomial.totalDegree
        (CPoly.fromCMvPolynomial g - CPoly.fromCMvPolynomial h) : ℕ) : ℚ)
      / (Fintype.card 𝔽 : ℚ) := by
  classical

  -- constant assignment embedding
  let const : 𝔽 → (Fin 1 → 𝔽) := fun r _ => r

  have hinj : Function.Injective const := by
    intro r s hrs
    have := congrArg (fun f => f 0) hrs
    simpa [const] using this

  -- bad r's (your LHS finset)
  let rBad : Finset 𝔽 :=
    {r ∈ (Finset.univ : Finset 𝔽) |
      verifier_expected_claim (𝔽 := 𝔽) g r
        = verifier_expected_claim (𝔽 := 𝔽) h r}

  -- bad assignments f : Fin 1 → 𝔽 (the finset appearing in one_round_soundness after simp)
  let fBad : Finset (Fin 1 → 𝔽) :=
    {f ∈ (Finset.univ : Finset (Fin 1 → 𝔽)) |
      CPoly.CMvPolynomial.eval f g = CPoly.CMvPolynomial.eval f h}

  -- Image of bad r's under const is contained in bad f's
  have hsubset : rBad.image const ⊆ fBad := by
    intro f hf
    rcases Finset.mem_image.mp hf with ⟨r, hr, rfl⟩
    have hr' :
        verifier_expected_claim (𝔽 := 𝔽) g r
          = verifier_expected_claim (𝔽 := 𝔽) h r :=
      (Finset.mem_filter.mp hr).2
    have : CPoly.CMvPolynomial.eval (const r) g = CPoly.CMvPolynomial.eval (const r) h := by
      -- rewrite verifier_expected_claim into eval-at-constant-assignment
      simpa [verifier_expected_claim_eq_eval (𝔽 := 𝔽) (p := g) (r := r),
            verifier_expected_claim_eq_eval (𝔽 := 𝔽) (p := h) (r := r),
            const] using hr'
    -- finish membership in fBad
    simp [fBad, this]

  have hcard : rBad.card ≤ fBad.card := by
    have hcard_image : (rBad.image const).card = rBad.card := by
      simpa using (Finset.card_image_of_injective rBad hinj)
    have : (rBad.image const).card ≤ fBad.card :=
      Finset.card_le_card hsubset
    simpa [hcard_image] using this

  -- turn card ≤ card into probability ≤ probability by dividing by |𝔽|
  have hprob_le :
      (↑rBad.card : ℚ) / (Fintype.card 𝔽 : ℚ)
        ≤ (↑fBad.card : ℚ) / (Fintype.card 𝔽 : ℚ) := by
    have hcardQ : (↑rBad.card : ℚ) ≤ (↑fBad.card : ℚ) := by
      exact_mod_cast hcard
    have hden : (0 : ℚ) ≤ (Fintype.card 𝔽 : ℚ) := by
      exact_mod_cast (Nat.zero_le (Fintype.card 𝔽))
    exact div_le_div_of_nonneg_right hcardQ hden

  -- apply the all-assignments soundness bound
  have hall :
      (↑fBad.card : ℚ) / (Fintype.card 𝔽 : ℚ)
        ≤ ((MvPolynomial.totalDegree
              (CPoly.fromCMvPolynomial g - CPoly.fromCMvPolynomial h) : ℕ) : ℚ)
            / (Fintype.card 𝔽 : ℚ) := by
    simpa [fBad] using one_round_soundness (𝔽 := 𝔽) (g := g) (h := h) hgh

  -- unfold rBad back to your original statement
  simpa [rBad] using le_trans hprob_le hall
