import CompPoly.Multivariate.Unlawful
import CompPoly.Multivariate.Lawful
import ExtTreeMapLemmas.ExtTreeMap

namespace Sumcheck

open CPoly
open Std

namespace CPoly.Unlawful

variable {n : ℕ} {R : Type _}
variable [Zero R] [BEq R] [LawfulBEq R]

lemma getElem?_fromUnlawful (u : CPoly.Unlawful n R) (m : CPoly.CMvMonomial n) :
  (CPoly.Lawful.fromUnlawful (n := n) (R := R) u).1[m]?
    = Option.filter (fun c => c != 0) u[m]? := by
  unfold CPoly.Lawful.fromUnlawful
  -- Now LHS is `(Std.ExtTreeMap.filter (fun _ c => c != 0) u)[m]?`
  -- The library lemma has RHS `Option.filter ((fun _ c => c != 0) m) u[m]?`,
  -- so we align the goal with a `change` and then `exact` it.
  change (Std.ExtTreeMap.filter (fun (_ : CPoly.CMvMonomial n) (c : R) => c != 0) u)[m]?
      = Option.filter ((fun (_ : CPoly.CMvMonomial n) (c : R) => c != 0) m) u[m]?
  exact (Std.ExtTreeMap.getElem?_filter_with_getKey
    (f := fun (_ : CPoly.CMvMonomial n) (c : R) => c != 0)
    (k := m) (m := u))

lemma mem_fromUnlawful_imp_exists_coeff
  (u : CPoly.Unlawful n R) (m : CPoly.CMvMonomial n) :
  m ∈ (CPoly.Lawful.fromUnlawful (n := n) (R := R) u)
    → ∃ v : R, v ≠ 0 ∧ u[m]? = some v := by
  intro hm
  classical
  rcases (CPoly.Lawful.mem_iff
      (p := CPoly.Lawful.fromUnlawful (n := n) (R := R) u) (x := m)).1 hm with
    ⟨v, hv0, hv_some⟩
  -- rewrite hv_some using getElem?_fromUnlawful
  have hv_filter :
      Option.filter (fun c => c != 0) u[m]? = some v := by
    -- IMPORTANT: plain rewrite, no `simpa` that can collapse to True
    exact (by
      -- hv_some : (fromUnlawful u).1[m]? = some v
      -- rewrite LHS
      simpa [getElem?_fromUnlawful (n := n) (R := R) u m] using hv_some)

  -- now destruct u[m]? and read off the witness
  cases h : u[m]? with
  | none =>
      -- filter none = none, contradiction
      simp [h] at hv_filter
  | some w =>
      -- First rewrite hv_filter so it talks about (some w)
      have hv_filter' : Option.filter (fun c => c != 0) (some w) = some v := by
        -- IMPORTANT: plain rewrite, no simp lemmas about filter_eq_some
        exact (by simpa [h] using hv_filter)

      -- Now do a controlled case split on (w != 0)
      by_cases hne : (w != 0) = true
      · -- unfold Option.filter, and rewrite using hne
        have hw_eq : some w = some v := by
          -- unfold Option.filter *as a definition*, so it becomes an if-then-else
          -- then rewrite with hne
          -- This avoids simp rewriting into ∧
          simpa [Option.filter, hne] using hv_filter'
        have hwv : w = v := by
          exact Option.some.inj hw_eq
        refine ⟨v, hv0, ?_⟩
        -- u[m]? = some v (rewrite h using hwv)
        simp [hwv]
      · -- if w != 0 is false, filter returns none, contradiction
        have : Option.filter (fun c => c != 0) (some w) = none := by
          simp [Option.filter, hne]
        -- contradict hv_filter'
        cases hv_filter' ▸ this

-- /-- If a monomial survives the `fromUnlawful` filter, it was present in the original map. -/
-- lemma mem_fromUnlawful_imp_mem_unlawful
--   (u : CPoly.Unlawful n R) (m : CPoly.CMvMonomial n) :
--   m ∈ (CPoly.Lawful.fromUnlawful (n := n) (R := R) u) → m ∈ u := by
--   intro hm
--   classical


-- lemma mem_add_imp {m : CMvMonomial n} (p q : CPoly.Unlawful n R) :
--   m ∈ (p + q) → m ∈ p ∨ m ∈ q := by
--   intro hmem
--   classical
--   #check ExtTreeMap.getElem?_filter
--   -- rewrite + into mergeWith
--   have hmem' :
--       m ∈ p.mergeWith (fun _ c₁ c₂ => c₁ + c₂) q := by
--     simpa [CPoly.Unlawful.grind_add_skip] using hmem

--   -- turn membership into isSome(getElem?)
--   have hm_some : (p.mergeWith (fun _ c₁ c₂ => c₁ + c₂) q)[m]?.isSome := by
--     -- this lemma is used elsewhere in CompPoly/Lawful.lean
--     simpa [Std.ExtTreeMap.mem_iff_isSome_getElem?] using hmem'

--   -- case split on whether key is in p and/or q by splitting getElem?
--   by_cases hp : p[m]?.isSome
--   · -- then m ∈ p
--     have : m ∈ p := by
--       simpa [Std.ExtTreeMap.mem_iff_isSome_getElem?] using hp
--     exact Or.inl this
--   · by_cases hq : q[m]?.isSome
--     · have : m ∈ q := by
--         simpa [Std.ExtTreeMap.mem_iff_isSome_getElem?] using hq
--       exact Or.inr this
--     · -- neither isSome, so mergeWith getElem? should be none, contradiction
--       -- This is the critical simp step:
--       --   (mergeWith ...)[m]? = none when both sides are none
--       have : (p.mergeWith (fun _ c₁ c₂ => c₁ + c₂) q)[m]? = none := by
--         -- `simp` should use the mergeWith getElem? lemma from ExtTreeMapLemmas
--         -- plus hp/hq turned into getElem? = none
--         have hp0 : p[m]? = none := by
--           cases h : p[m]? <;> simp [h] at hp
--         have hq0 : q[m]? = none := by
--           cases h : q[m]? <;> simp [h] at hq
--         simp [hp0, hq0]
--       -- but then it can't be isSome
--       have : False := by simpa [this] using hm_some
--       exact False.elim this


end CPoly.Unlawful

end Sumcheck
