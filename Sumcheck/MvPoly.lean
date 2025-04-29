import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Lattice.Union

open MvPolynomial Finset
open Finset

@[simp]
lemma biUnion_union {α β : Type*} [DecidableEq α] [DecidableEq β]
  (s t : Finset α) (f : α → Finset β) :
  (s ∪ t).biUnion f = s.biUnion f ∪ t.biUnion f := by
  ext x
  -- reduce membership to pure ∃/∨/∧
  simp only [mem_union, mem_biUnion]
  -- now do the propositional splitting
  constructor
  · -- (→) direction
    rintro ⟨a, (ha | ha), hxa⟩
    · exact Or.inl ⟨a, ha, hxa⟩
    · exact Or.inr ⟨a, ha, hxa⟩
  · -- (←) direction
    rintro (⟨a, ha, hxa⟩ | ⟨a, ha, hxa⟩)
    · exact ⟨a, Or.inl ha, hxa⟩
    · exact ⟨a, Or.inr ha, hxa⟩

-- Define a function "arity" with two type parameters σ and R
-- σ represents variable names and R coefficients
-- You must be able to compare the variable names to count them
-- You must be able to do arithmetic +,-,*,/ on R due to the definition of MvPolynomial σ R
-- arity is the cardinality of the union of used variables in all of the monomials of p
def arity {σ R : Type*} [DecidableEq σ] [CommSemiring R]
  (p : MvPolynomial σ R) : ℕ :=
  (p.support.biUnion (fun m => m.support)).card

-- Define a lemma for "The arity of the zero polynomial is zero"
-- The goal is that if we feed the zero polynomial to the def "arity", the result is zero
-- tactic "unfold" rewrites goal like (p.support.biUnion (fun m => m.support)).card = 0
-- tactic "simp" simplifies the goal using facts support 0 = ∅ and biUnion ∅ f = ∅
-- so by substitution ∅.biUnion f = ∅ and ∅.card = 0
lemma arity_zero {σ R : Type*} [DecidableEq σ] [CommSemiring R] :
  arity (0 : MvPolynomial σ R) = 0 := by
  unfold arity
  simp [support_zero, Finset.biUnion_empty]

-- Define a lemma for "The arity of the sum of two polynomials is less than or equal to the sum of their arities"
-- The goal is that if we feed the sum of two polynomials to the def "arity", the result is less than or equal to the sum of their arities
-- tactic "unfold" rewrites goal like (p + q).support.biUnion (fun m => m.support) ≤ p.support.biUnion (fun m => m.support) + q.support.biUnion (fun m => m.support)
lemma arity_add {σ R : Type*} [DecidableEq σ] [CommSemiring R]
  (p q : MvPolynomial σ R) :
  arity (p + q) ≤ arity p + arity q := by
  unfold arity

  -- p+q support ⊆ p.support ∪ q.support
  have h1 : (p + q).support ⊆ p.support ∪ q.support := support_add
  -- push that subset through biUnion
  have h2 : (p + q).support.biUnion Finsupp.support
          ⊆ (p.support ∪ q.support).biUnion Finsupp.support :=
    biUnion_subset_biUnion_of_subset_left Finsupp.support h1

  -- now take cards
  have h3 := card_mono h2

  -- distribute the union into two biUnions
  have h4 := biUnion_union (p.support) (q.support) (fun m => Finsupp.support m)

  -- rewrite the RHS of h3 using h4 and finish with the union‐card bound
  calc
    ((p + q).support.biUnion Finsupp.support).card
        ≤ ((p.support ∪ q.support).biUnion Finsupp.support).card := h3
    _   = (p.support.biUnion Finsupp.support ∪ q.support.biUnion Finsupp.support).card := by rw [h4]
    _   ≤ (p.support.biUnion Finsupp.support).card + (q.support.biUnion Finsupp.support).card := card_union_le _ _

-- def vars {σ R : Type*} [DecidableEq σ] [CommSemiring R]
--   (p : MvPolynomial σ R) : Finset σ :=
--   p.support.biUnion fun m => m.support

-- abbrev dom {σ R : Type*} [CommSemiring R] (θ : σ →₀ R) : Finset σ := θ.support

-- noncomputable def inst {σ R : Type*} [DecidableEq σ] [CommSemiring R]
--   (p : MvPolynomial σ R) (θ : σ →₀ R) : MvPolynomial σ R :=
--   --   ring‐map    variables ↦ constant polynomials
--   eval₂Hom (C : R →+* MvPolynomial σ R) (fun i => C (θ i)) p

-- /-- `vars p` is definitionally the union of the supports of its monomials. -/
-- @[simp]
-- lemma vars_def {σ R : Type*} [DecidableEq σ] [CommSemiring R]
--   (p : MvPolynomial σ R) :
--   _root_.vars p = p.support.biUnion fun m => m.support := rfl

-- /-- `arity p` is definitionally the cardinality of `vars p`. -/
-- @[simp]
-- lemma arity_def {σ R : Type*} [DecidableEq σ] [CommSemiring R]
--   (p : MvPolynomial σ R) :
--   arity p = (_root_.vars p).card := rfl

-- /-- Instantiating `p` by a finitely-supported substitution `θ` removes exactly the variables
-- in `θ.support` from `vars p`. -/
-- @[simp]
-- lemma vars_inst {σ R : Type*} [DecidableEq σ] [CommSemiring R]
--   (p : MvPolynomial σ R) (θ : σ →₀ R) :
--   (inst p θ).vars = p.vars \ θ.support := by
--   -- by definition `vars p = p.support.biUnion support`, and
--   -- inst p θ = eval₂Hom C (fun i => C (θ i)) p,
--   -- and one shows easily that `eval₂Hom` does *not* introduce any new variables,
--   -- and kills exactly those in `θ.support`.
--   dsimp [inst, _root_.vars]
--   -- now p.support.biUnion support is the same on both sides except that
--   -- we only keep those monomials whose `support` is disjoint from θ.support,
--   -- which is exactly the set-difference on the outer finset.
--   simp only [support_eval₂Hom, support_C, support_X, support_mul, support_add,
--              Finsupp.support, Finsupp.mem_support_iff,
--              biUnion_subset_biUnion_of_subset_left, Finsupp.support_map,
--              Finset.filter, Finset.filter_eq, Finset.sdiff_eq_filter,
--              Finset.mem_sdiff, Finset.mem_filter]

-- lemma arity_inst {σ R : Type*} [DecidableEq σ] [CommSemiring R]
--   (p : MvPolynomial σ R) (θ : σ →₀ R) (h : θ.support ⊆ vars p) :
--   arity (inst p θ) ≤ arity p - θ.support.card := by
--   simp only [arity_def, vars_inst]  -- now everything is at the Finset level
--   exact (card_sdiff_of_subset h).le

-- noncomputable def inst {σ R : Type*}
--   [DecidableEq σ] [CommSemiring R]
--   (p : MvPolynomial σ R) (θ : σ →₀ R) : MvPolynomial σ R :=
-- -- replace each variable by the constant polynomial `C (θ i)`
--   eval₂Hom (C : R →+* MvPolynomial σ R) (fun i => C (θ i)) p

-- -- @[simp]
-- -- lemma vars_inst {σ R : Type*} [DecidableEq σ] [CommSemiring R]
-- --   (p : MvPolynomial σ R) (θ : σ →₀ R) :
-- --   (inst p θ).vars = ∅ := by
-- -- -- every X _ goes to (C _), so `eval₂Hom` produces sums/products of `C _`,
-- -- -- and `simp` knows `vars (C _) = ∅` plus `vars (a + b) = vars a ∪ vars b`.
-- --   simp [inst]

-- @[simp]
-- lemma vars_inst {σ R : Type*} [DecidableEq σ] [CommSemiring R]
--   (p : MvPolynomial σ R) (θ : σ →₀ R) :
--   (inst p θ).vars = ∅ := by
--   -- by definition `inst p θ = eval₂Hom C (fun i => C (θ i)) p`
--   dsimp [inst]
--   -- now we do induction on `p`
--   induction p using MvPolynomial.induction_on with
--   | C a => -- constant case
--     simp [inst]  -- inst (C a) θ = C a
--   | mul_X i p ih =>
--     -- here p is what remains inside the X-constructor
--     simp [inst]  -- inst (X i) θ = C (θ i)
--   | add p q ihp ihq =>
--     simp [inst, *] -- variables of sum is union

-- @[simp] lemma arity_def {σ R : Type*}
--   [DecidableEq σ] [CommSemiring R] (p : MvPolynomial σ R) :
--   arity p = p.vars.card := rfl

-- lemma arity_inst {σ R : Type*}
--   [DecidableEq σ] [CommSemiring R]
--   (p : MvPolynomial σ R) (θ : σ →₀ R) :
--   arity (inst p θ) ≤ arity p - θ.support.card := by
--   simp [arity_def, vars_inst]
--   -- goal becomes `0 ≤ p.vars.card - θ.support.card`,
--   -- which follows from `θ.support ⊆ p.vars` and `Nat.sub_le_sub_right`.
--   exact (card_sdiff_of_subset (Finset.support_subset _)).le





noncomputable def arity {σ R : Type*} [DecidableEq σ] [CommSemiring R]
  (p : MvPolynomial σ R) : ℕ :=
  p.vars.card


@[simp]
lemma arity_zero {σ R : Type*} [DecidableEq σ] [CommSemiring R] :
  arity (0 : MvPolynomial σ R) = 0 := by
  -- vars_zero : (0 : MvPolynomial σ R).vars = ∅
  simp [arity]

lemma arity_add {σ R : Type*} [DecidableEq σ] [CommSemiring R]
  (p q : MvPolynomial σ R) :
  arity (p + q) ≤ arity p + arity q := by
  -- arity (p + q) = (p + q).vars.card, arity p = p.vars.card, etc.
  simp only [arity]
  -- vars_add_subset : (p + q).vars ⊆ p.vars ∪ q.vars
  -- card_mono      : card A ≤ card B when A ⊆ B
  -- card_union_le  : card (p.vars ∪ q.vars) ≤ p.vars.card + q.vars.card
  calc
    (p + q).vars.card
        ≤ (p.vars ∪ q.vars).card := card_mono (vars_add_subset p q)
    _   ≤ p.vars.card + q.vars.card   := card_union_le _ _
