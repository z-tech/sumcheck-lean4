import Mathlib.Data.ZMod.Basic

import Sumcheck.Theorems.Universe.Polynomials

@[simp]
def num_possible_assignments
  {𝔽} (n : ℕ) [Fintype 𝔽] [DecidableEq 𝔽] : ℕ :=
  (all_assignments_n n 𝔽).card
