import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation

@[simp]
def hypercube_n {𝔽} [CommSemiring 𝔽] [DecidableEq 𝔽] (n : ℕ) : Finset (Fin n → 𝔽) :=
  Fintype.piFinset (fun _ : Fin n => ({0, 1} : Finset 𝔽))
