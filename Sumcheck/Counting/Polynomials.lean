import Mathlib.Data.ZMod.Basic

import Sumcheck.Universe.Polynomials

@[simp]
def count_assignments
  {𝔽} (n : ℕ) [Fintype 𝔽] [DecidableEq 𝔽] : ℕ :=
  (all_assignments_n n 𝔽).card
