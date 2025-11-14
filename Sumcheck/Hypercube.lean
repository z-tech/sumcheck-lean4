import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.ZMod.Basic

@[simp]
def generate_hypercube {𝔽} [CommSemiring 𝔽] [DecidableEq 𝔽] (n : ℕ) : Finset (Fin n → 𝔽) :=
  Fintype.piFinset (fun _ : Fin n => ({0, 1} : Finset 𝔽))

@[simp]
def generate_point {𝔽} [CommRing 𝔽] [DecidableEq 𝔽] (challenges : Fin k → 𝔽) (hypercube_point : Fin n → 𝔽) (_hcard : k ≤ n) : Fin n → 𝔽 :=
  fun i =>
    if h : (i.1 < k) then
      let j : Fin k := ⟨i.1, h⟩
      if hypercube_point i = (0 : 𝔽) then
        (1 : 𝔽) - challenges j
      else
        challenges j
    else
      hypercube_point i

namespace __HypercubeTests__

  namespace __generate_hypercube_tests__
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
  end __generate_hypercube_tests__

  namespace __generate_point_tests__
    noncomputable def point_0 : Fin 4 → (ZMod 19) := ![0, 1, 1, 0]
    noncomputable def challenges_0 : Fin 2 → (ZMod 19) := ![2, 7]
    noncomputable def expected_point_0 : Fin 4 → (ZMod 19) := ![1 - 2, 7, 1, 0]
    lemma it_generate_point_correctly_0 : generate_point challenges_0 point_0 (by decide) = expected_point_0 := by
      decide

    noncomputable def point_1 : Fin 4 → (ZMod 19) := ![0, 1, 1, 0]
    noncomputable def challenges_1 : Fin 0 → (ZMod 19) := ![]
    noncomputable def expected_point_1 : Fin 4 → (ZMod 19) := ![0, 1, 1, 0]
    lemma it_generate_point_correctly_1 : generate_point challenges_1 point_1 (by decide) = expected_point_1 := by
      decide
  end __generate_point_tests__

end __HypercubeTests__
