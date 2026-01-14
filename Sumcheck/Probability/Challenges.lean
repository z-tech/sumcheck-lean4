import Mathlib.Data.Rat.Init
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Filter

import Sumcheck.Universe.Polynomials

-- out of all possible challenge vectors len n, what fraction satisfy the event
noncomputable def prob_over_challenges
  {𝔽 : Type _} {n : ℕ} [Fintype 𝔽]
  (E : (Fin n → 𝔽) → Prop) : ℚ :=
by
  classical
  let Ω : Finset (Fin n → 𝔽) := all_assignments_n (𝔽 := 𝔽) n
  exact ((Ω.filter E).card : ℚ) / (Ω.card : ℚ)

@[simp] lemma prob_over_challenges_eq
  {𝔽 : Type _} {n : ℕ} [Fintype 𝔽]
  (E : (Fin n → 𝔽) → Prop) :
  prob_over_challenges (𝔽 := 𝔽) (n := n) E
    =
    (by
      classical
      let Ω : Finset (Fin n → 𝔽) := all_assignments_n (𝔽 := 𝔽) n
      exact ((Ω.filter E).card : ℚ) / (Ω.card : ℚ)) := by
  -- this is definitional unfolding
  rfl
