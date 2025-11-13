import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.ZMod.Basic

@[simp]
def generate_hypercube {𝔽} [CommSemiring 𝔽] [DecidableEq 𝔽] (n : ℕ) : Finset (Fin n → 𝔽) :=
  Fintype.piFinset (fun _ : Fin n => ({0, 1} : Finset 𝔽))

namespace __HypercubeTests__

  noncomputable def expected_hypercube_0 : Finset (Fin 0 → ZMod 19) := { (Fin.elim0 : Fin 0 → ZMod 19) }
  lemma it_should_generate_hypercube_0_correctly : generate_hypercube 0 = expected_hypercube_0 := by
    decide

  noncomputable def expected_hypercube_1 : Finset (Fin 1 → ZMod 19) := { ![0], ![1] }
  lemma it_should_generate_hypercube_1_correctly : generate_hypercube 1 = expected_hypercube_1 := by
    decide

  noncomputable def expected_hypercube_2 : Finset (Fin 2 → ZMod 19) := { ![0, 0], ![0, 1], ![1, 0], ![1, 1] }
  lemma it_should_generate_hypercube_2_correctly : generate_hypercube 2 = expected_hypercube_2 := by
    decide

  noncomputable def expected_hypercube_3 : Finset (Fin 3 → ZMod 19) := { ![0, 0, 0], ![0, 0, 1], ![0, 1, 0], ![0, 1, 1], ![1, 0, 0], ![1, 0, 1], ![1, 1, 0], ![1, 1, 1] }
  lemma it_should_generate_hypercube_3_correctly : generate_hypercube 3 = expected_hypercube_3 := by
    decide


end __HypercubeTests__
