import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.ZMod.Basic


@[simp]
def natToBoolVec (n : ℕ) (k : ℕ) : Fin n → Bool :=
  fun i => Nat.testBit k i

@[simp]
def natToPoint  {𝔽} [CommSemiring 𝔽] (n : ℕ) (num_bits : ℕ) : Fin n → 𝔽 :=
  fun i => if natToBoolVec n num_bits i then (1 : 𝔽) else (0 : 𝔽)

@[simp]
def generate_hypercube {𝔽} [CommSemiring 𝔽] [DecidableEq 𝔽] (n: ℕ) : Finset (Fin n → 𝔽) :=
  (Finset.range (Nat.pow 2 n)).image
    (fun k => natToPoint (𝔽 := 𝔽) n k)

namespace HypercubeTests

  lemma natToPoint_apply {𝔽} [CommSemiring 𝔽]
      (n k : ℕ) (i : Fin n) :
    natToPoint (𝔽 := 𝔽) n k i =
      (if Nat.testBit k i then (1 : 𝔽) else 0) := rfl

  @[simp] lemma natToPoint_zero {𝔽} [CommSemiring 𝔽] (k : ℕ) :
    natToPoint (𝔽 := 𝔽) 0 k = (Fin.elim0 : Fin 0 → 𝔽) := by
    funext i
    cases i with
    | mk val isLt =>
      cases isLt

  noncomputable def expected_hypercube_0 : Finset (Fin 0 → ZMod 19) := { (Fin.elim0 : Fin 0 → ZMod 19) }
  lemma it_should_generate_hypercube_0_correctly : generate_hypercube 0 = expected_hypercube_0 := by
    unfold generate_hypercube expected_hypercube_0
    simp

  noncomputable def expected_hypercube_1 : Finset (Fin 1 → ZMod 19) := { ![0], ![1] }
  -- TODO z-tech
  -- lemma it_should_generate_hypercube_1_correctly : generate_hypercube 1 = expected_hypercube_1 := by
  --   unfold generate_hypercube expected_hypercube_1
  --   simp [Finset.range, Finset.image, natToPoint_apply, Nat.pow_one]


end HypercubeTests
