import Mathlib.Data.ZMod.Basic

import Sumcheck.Properties.Probability.Universe

@[simp] def countAllAssignmentsN
  {𝔽} (n : ℕ) [Fintype 𝔽] [DecidableEq 𝔽] : ℕ :=
  (allAssignmentsN n 𝔽).card
