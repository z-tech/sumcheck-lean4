import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.ZMod.Basic

open Polynomial

variable {𝔽 : Type} [Field 𝔽]

/-- Definition --/
structure IOR (𝒪 𝒬 𝒜 𝒞 : Type) where
  (oracle : 𝒪 → 𝒜)
  (verifier_move : 𝒬)
  (verifier_check : (𝒪 → 𝒜) → 𝒬 → 𝒜 → Bool)
  (expected : 𝒜)
  (challenge: 𝒞)

/-- Instantiation --/
noncomputable def test_polynomial : Polynomial (ZMod 7) := X ^ 2 + 1
noncomputable def test_oracle : (ZMod 7) → (ZMod 7) := λ x => Polynomial.eval x test_polynomial
noncomputable def test_IOR : IOR (ZMod 7) (List (ZMod 7)) (ZMod 7) (ZMod 7) :=
let expected := test_oracle (3: ZMod 7)
{ oracle := test_oracle,
  verifier_move := [0, 1],
  verifier_check := λ o q _a => decide (o q.head! + o q.tail.head! = expected),
  expected := expected
  challenge := 3
}
