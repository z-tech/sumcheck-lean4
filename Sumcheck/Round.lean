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

@[simp] def field_size {𝔽} [Fintype 𝔽] : ℚ :=
  (Fintype.card 𝔽 : ℚ)

@[simp] def all_possible_assignments_n (n : ℕ) (𝔽 : Type _) [Fintype 𝔽] :
  Finset (Fin n → 𝔽) := Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset 𝔽))

-- coerces Lean types in some way that's needed
@[simp] lemma all_possible_assignments_n_eq_univ
  (n : ℕ) (𝔽 : Type _) [Fintype 𝔽] [DecidableEq 𝔽] :
  all_possible_assignments_n n 𝔽 = (Finset.univ : Finset (Fin n → 𝔽)) := by
  classical
  ext f
  simp [all_possible_assignments_n]

@[simp] def num_possible_assignments
  {𝔽} (n : ℕ) [Fintype 𝔽] [DecidableEq 𝔽] : ℕ :=
  (all_possible_assignments_n n 𝔽).card

@[simp] def assignment_causes_agreement
  {n} {𝔽} [CommRing 𝔽]
  (g h : CPoly.CMvPolynomial n 𝔽)
  (assignment : Fin n → 𝔽) : Prop :=
  CPoly.CMvPolynomial.eval assignment g = CPoly.CMvPolynomial.eval assignment h

-- makes the above proposition decidable in some way that's needed
@[simp] instance assignment_causes_agreement_decidable
  {n} {𝔽} [CommRing 𝔽] [DecidableEq 𝔽]
  (g h : CPoly.CMvPolynomial n 𝔽) :
  DecidablePred (fun assignment : Fin n → 𝔽 =>
    assignment_causes_agreement (g := g) (h := h) assignment) := by
  intro assignment
  dsimp [assignment_causes_agreement]
  infer_instance

@[simp] def num_assignments_that_cause_agreement
  {n} {𝔽} [CommRing 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (g h : CPoly.CMvPolynomial n 𝔽) : ℕ :=
  {assignment ∈ all_possible_assignments_n n 𝔽
    | assignment_causes_agreement (g := g) (h := h) assignment}.card

@[simp] def prob_agreement
  {n} {𝔽} [CommRing 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (g h : CPoly.CMvPolynomial n 𝔽)
  (_h_not_equal : g ≠ h) : ℚ :=
  num_assignments_that_cause_agreement g h / num_possible_assignments (𝔽 := 𝔽) n

@[simp] noncomputable def difference_poly
  {n : ℕ} {𝔽 : Type _} [CommRing 𝔽]
  (g h : CPoly.CMvPolynomial n 𝔽) : MvPolynomial (Fin n) 𝔽 :=
  CPoly.fromCMvPolynomial g - CPoly.fromCMvPolynomial h

lemma difference_poly_eq_zero_iff
  {n : ℕ} {𝔽 : Type _} [CommRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (g h : CPoly.CMvPolynomial n 𝔽) :
  difference_poly g h = (0 : MvPolynomial (Fin n) 𝔽) ↔ g = h := by
  constructor
  · intro hd
    have hfrom :
        CPoly.fromCMvPolynomial g = CPoly.fromCMvPolynomial h := by
      exact sub_eq_zero.mp (by simpa [difference_poly] using hd)
    exact (CPoly.eq_iff_fromCMvPolynomial (u := g) (v := h)).2 hfrom
  · intro hgh
    subst hgh
    simp [difference_poly]

-- this is same as max_ind_degree when n=1
@[simp] noncomputable def total_degree_difference_poly
  {n : ℕ} {𝔽 : Type _} [CommRing 𝔽]
  (g h : CPoly.CMvPolynomial n 𝔽) : ℕ :=
  MvPolynomial.totalDegree (difference_poly g h)

@[simp] noncomputable def degree_over_field_size
  {n : ℕ} {𝔽 : Type _} [CommRing 𝔽] [Fintype 𝔽]
  (g h : CPoly.CMvPolynomial n 𝔽) : ℚ :=
  total_degree_difference_poly g h / field_size (𝔽 := 𝔽)

-- pr[ g(x) = h(x) ] ≤ deg(g - h) / |𝔽| from Schwartz-Zippel
lemma prob_agreement_le_degree_over_field_size
  {𝔽} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (g h : CPoly.CMvPolynomial 1 𝔽)
  (h_not_equal : g ≠ h) :
  prob_agreement g h h_not_equal ≤ degree_over_field_size g h :=
by
  classical
  have h_diff_non_zero : difference_poly g h ≠ (0 : MvPolynomial (Fin 1) 𝔽) := by
    intro h_assume_diff_zero
    have diff_zero_implies_eq : difference_poly g h = 0 → (g = h) := (difference_poly_eq_zero_iff g h).1
    have contra := h_not_equal (diff_zero_implies_eq h_assume_diff_zero)
    exact contra
  have sz := MvPolynomial.schwartz_zippel_totalDegree h_diff_non_zero (S := (Finset.univ : Finset 𝔽))
  simpa [CPoly.eval_equiv (p := g), CPoly.eval_equiv (p := h), sub_eq_zero] using sz

@[simp] lemma next_claim_eq_eval
  {𝔽} [CommRing 𝔽] [DecidableEq 𝔽]
  (challenge : 𝔽)
  (p : CPoly.CMvPolynomial 1 𝔽) :
  next_claim (𝔽 := 𝔽) challenge p
    = CPoly.CMvPolynomial.eval (fun _ : Fin 1 => challenge) p := by
  simp [next_claim, CPoly.CMvPolynomial.eval]

@[simp] def prob_next_claim_agreement
  {𝔽 : Type _} [Fintype 𝔽] [DecidableEq 𝔽] [CommRing 𝔽]
  (g h : CPoly.CMvPolynomial 1 𝔽) : ℚ :=
  {r ∈ (Finset.univ : Finset 𝔽) | next_claim r g = next_claim r h}.card
    / field_size (𝔽 := 𝔽)

-- pr[ next_claim g r = next_claim h r ] ≤ deg(g - h) / |𝔽| from prob_agreement_le_degree_over_field_size
@[simp] lemma next_claim_binding
  {𝔽 : Type _} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (g h : CPoly.CMvPolynomial 1 𝔽)
  (hgh : g ≠ h) : prob_next_claim_agreement g h
  ≤ MvPolynomial.totalDegree (difference_poly g h) / field_size (𝔽 := 𝔽) := by
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
      next_claim (𝔽 := 𝔽) r g
        = next_claim (𝔽 := 𝔽) r h}

  -- bad assignments f : Fin 1 → 𝔽 (the finset appearing in one_round_soundness after simp)
  let fBad : Finset (Fin 1 → 𝔽) :=
    {f ∈ (Finset.univ : Finset (Fin 1 → 𝔽)) |
      CPoly.CMvPolynomial.eval f g = CPoly.CMvPolynomial.eval f h}

  -- Image of bad r's under const is contained in bad f's
  have hsubset : rBad.image const ⊆ fBad := by
    intro f hf
    rcases Finset.mem_image.mp hf with ⟨r, hr, rfl⟩
    have hr' :
        next_claim (𝔽 := 𝔽) r g
          = next_claim (𝔽 := 𝔽) r h :=
      (Finset.mem_filter.mp hr).2
    have : CPoly.CMvPolynomial.eval (const r) g = CPoly.CMvPolynomial.eval (const r) h := by
      -- rewrite verifier_expected_claim into eval-at-constant-assignment
      simpa [next_claim_eq_eval r g, next_claim_eq_eval r h, const] using hr'
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
    simpa [fBad] using prob_agreement_le_degree_over_field_size (𝔽 := 𝔽) (g := g) (h := h) hgh

  -- unfold rBad back to your original statement
  simpa [rBad] using le_trans hprob_le hall
