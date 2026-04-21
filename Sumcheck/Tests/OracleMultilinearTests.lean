import Sumcheck.Oracle.Multilinear
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# Smoke tests for `Sumcheck.Oracle.Multilinear`

Concrete 2-variable / 3-variable end-to-end checks over `ZMod 19` that the
MSB half-split multilinear sumcheck oracle produces the expected transcript
on hand-computed inputs. Kernel-evaluable via `decide` / `rfl`.
-/

namespace __OracleMultilinearTests__

open Sumcheck.Oracle.Multilinear

instance : Fact (Nat.Prime 19) := ⟨by decide⟩

abbrev 𝔽 := ZMod 19

/-! ### 2-variable instance

`v : {0,1}² → 𝔽` given by `v(x₀, x₁) = 1 + 2·x₁ + 2·x₀ + 0·x₀x₁`, i.e.
evaluations `[v(0,0), v(0,1), v(1,0), v(1,1)] = [1, 2, 3, 4]` (MSB layout).

Challenges `w₀ = 5, w₁ = 6`.

Hand computation:
* Round 0: `s₀ = 1 + 2 = 3`, `s₁ = 3 + 4 = 7`. Check `s₀ + s₁ = 10` equals
  `Σ evals`.
* Fold by 5: `new = [1 + (3−1)·5, 2 + (4−2)·5] = [11, 12]`.
* Round 1: `s₀ = 11`, `s₁ = 12`. Check `s₀ + s₁ = 23` equals round-0 poly
  at `X = 5`: `3 + 5·(7−3) = 23`. ✓
* Fold by 6: `new = [11 + (12−11)·6] = [17]`.
* Final value = 17.
-/

def evals2 : Array 𝔽 := #[1, 2, 3, 4]
def challenges2 : Array 𝔽 := #[5, 6]

-- Round polynomials match hand computation.
example :
    (multilinearOracle evals2 challenges2).1 = #[(3, 7), (11, 12)] := by
  decide

-- Final value matches hand computation.
example : (multilinearOracle evals2 challenges2).2 = (17 : 𝔽) := by
  decide

/-! ### Consistency: `s₀ + s₁` per round equals the running claim. -/

-- Round 0 sum = Σ evals.
example :
    ((multilinearOracle evals2 challenges2).1[0]!.1
      + (multilinearOracle evals2 challenges2).1[0]!.2) =
      (evals2[0]! + evals2[1]! + evals2[2]! + evals2[3]!) := by
  decide

end __OracleMultilinearTests__
