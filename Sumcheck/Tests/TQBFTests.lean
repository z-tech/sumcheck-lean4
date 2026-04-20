import Mathlib.Data.Fin.VecNotation
import Sumcheck.IP.TQBF

-- End-to-end smoke tests for the TQBF semantics. Verifies that `value` and
-- `Valid` reduce on concrete small formulas with known truth values.

namespace __TQBFTests__

open TQBF SharpSAT

-- Helper: build a single-variable literal.
private def lit (v : Fin n) (pol : Bool) : Literal n := { var := v, pol := pol }

-- Helper: a Clause3 whose three literals are all the same single literal — so
-- the clause is equivalent to that one literal. Useful for tiny test matrices.
private def triClause {n : ℕ} (ℓ : Literal n) : Clause3 n :=
  { ℓ₁ := ℓ, ℓ₂ := ℓ, ℓ₃ := ℓ }

-- `∃x. x` — true (pick x = true).
def existsTrue : QBF 1 :=
  { quantifiers := fun _ => .«exists»
    matrix := [triClause (lit 0 true)] }

example : existsTrue.value = true := by decide
example : existsTrue.Valid := by decide

-- `∀x. x` — false (fails at x = false).
def forallFalse : QBF 1 :=
  { quantifiers := fun _ => .«forall»
    matrix := [triClause (lit 0 true)] }

example : forallFalse.value = false := by decide
example : ¬ forallFalse.Valid := by decide

-- `∀x ∃y. y` — true (the inner ∃y y doesn't depend on x).
def forallExists : QBF 2 :=
  { quantifiers := ![.«forall», .«exists»]
    matrix := [triClause (lit 1 true)] }

example : forallExists.value = true := by decide
example : forallExists.Valid := by decide

-- `∃y ∀x. y` — also true (pick y = true, then ∀x y = true).
def existsForall : QBF 2 :=
  { quantifiers := ![.«exists», .«forall»]
    matrix := [triClause (lit 0 true)] }

example : existsForall.value = true := by decide

end __TQBFTests__
