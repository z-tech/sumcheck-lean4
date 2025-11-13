import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.ZMod.Basic

@[simp]
def nat_to_bool_vec (n : ℕ) (k : ℕ) : Fin n → Bool :=
  fun i => Nat.testBit k i

@[simp]
def nat_to_point  {𝔽} [CommSemiring 𝔽] (n : ℕ) (num_bits : ℕ) : Fin n → 𝔽 :=
  fun i => if nat_to_bool_vec n num_bits i then (1 : 𝔽) else (0 : 𝔽)

@[simp]
def generate_hypercube {𝔽} [CommSemiring 𝔽] [DecidableEq 𝔽] (n: ℕ) : Finset (Fin n → 𝔽) :=
  (Finset.range (Nat.pow 2 n)).image
    (fun k => nat_to_point (𝔽 := 𝔽) n k)

namespace __HypercubeTests__

  noncomputable def expected_hypercube_0 : Finset (Fin 0 → ZMod 19) := { (Fin.elim0 : Fin 0 → ZMod 19) }
  lemma it_should_generate_hypercube_0_correctly : generate_hypercube 0 = expected_hypercube_0 := by
    unfold generate_hypercube expected_hypercube_0 nat_to_point nat_to_bool_vec
    simp
    funext i
    cases i with
    | mk val isLt =>
      cases isLt

  noncomputable def expected_hypercube_1 : Finset (Fin 1 → ZMod 19) := { ![0], ![1] }
  lemma it_should_generate_hypercube_1_correctly : generate_hypercube 1 = expected_hypercube_1 := by
    unfold generate_hypercube expected_hypercube_1 nat_to_point nat_to_bool_vec
    simp [Finset.range, Finset.image]
    aesop

  -- TODO (z-tech): must convince how hypercube is generated in a generic way
  -- noncomputable def expected_hypercube_2 : Finset (Fin 2 → ZMod 19) := { ![0, 0], ![0, 1], ![1, 0], ![1, 1] }
  -- lemma it_should_generate_hypercube_2_correctly : generate_hypercube 2 = expected_hypercube_2 := by
  --   unfold generate_hypercube expected_hypercube_2 nat_to_point nat_to_bool_vec
  --   simp [Finset.range, Finset.image, Nat.testBit]


end __HypercubeTests__
