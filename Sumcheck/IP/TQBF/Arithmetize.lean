import Sumcheck.IP.TQBF.QBF
import Sumcheck.IP.TQBF.Linearize
import Sumcheck.IP.SharpSAT.Arithmetize

/-!
# Shamir arithmetization of TQBF

Arithmetize a TQBF formula to a field element — 1 if the formula is valid,
0 otherwise. The recursion peels off the outermost quantifier, recursively
arithmetizes each branch (x₀ = 0 and x₀ = 1), then combines with the
quantifier's arithmetic analogue:

* `∀` becomes product: `A₀ · A₁`
* `∃` becomes `1 - (1 - A₀)(1 - A₁)` (one-minus-product-of-one-minuses)

The matrix is arithmetized by the existing `SharpSAT.arithmetize`, which
already yields `1` for satisfying assignments and `0` otherwise.

## Scope note — no linearization yet

This recursion produces a polynomial of exponential degree (each ∀/∃ step
doubles individual degree). That's fine for *correctness* — the value is the
same — but disastrous for sumcheck soundness. The Shamir protocol inserts a
`linearize` operator between quantifier steps to keep degrees polynomial.
Wiring that in requires generalizing `linearize0` to arbitrary variable index
(via `CompPoly.Rename`), which is the natural next piece of work.

## Key theorems

* `arithmetizeQBFAux_eval` — the correctness invariant, parametrized over an
  abstract boolean function and its polynomial arithmetization. Used for
  structural induction on the quantifier prefix length.
* `arithmetizeQBF_eq_boolToField_value` — the main theorem: the arithmetization
  of a QBF, evaluated at the empty assignment, equals `boolToField Q.value`.
-/

namespace TQBF

open CPoly SharpSAT

variable {𝔽 : Type} [Field 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]

/-- Core arithmetization recursion: given a quantifier prefix of length `n`
and a polynomial `p : CMvPolynomial n 𝔽`, produce a scalar (`CMvPolynomial 0 𝔽`)
representing the quantified-formula value. -/
noncomputable def arithmetizeQBFAux :
    (n : ℕ) → (Fin n → Quantifier) → CMvPolynomial n 𝔽 → CMvPolynomial 0 𝔽
  | 0, _, p => p
  | _ + 1, pre, p =>
    let A0 := arithmetizeQBFAux _ (fun i => pre i.succ)
                (CMvPolynomial.specialize0 p 0)
    let A1 := arithmetizeQBFAux _ (fun i => pre i.succ)
                (CMvPolynomial.specialize0 p 1)
    match pre 0 with
    | .«forall» => A0 * A1
    | .«exists» => 1 - (1 - A0) * (1 - A1)

/-- Full QBF arithmetization: compose with the matrix arithmetization. -/
noncomputable def arithmetizeQBF {n : ℕ} (Q : QBF n) : CMvPolynomial 0 𝔽 :=
  arithmetizeQBFAux n Q.quantifiers (SharpSAT.arithmetize (𝔽 := 𝔽) Q.matrix)

/-- **Correctness invariant.** If a polynomial `p` encodes a boolean function
`f` (meaning `p.eval (boolToField ∘ x) = boolToField (f x)` at every boolean
input), then the arithmetized quantifier prefix, evaluated at the empty
assignment, equals `boolToField (valueAt n pre f)`. -/
theorem arithmetizeQBFAux_eval :
    ∀ (n : ℕ) (pre : Fin n → Quantifier) (p : CMvPolynomial n 𝔽)
      (f : (Fin n → Bool) → Bool),
      (∀ x, p.eval (fun i => boolToField (x i)) = boolToField (f x)) →
      (arithmetizeQBFAux n pre p).eval Fin.elim0 =
        boolToField (valueAt n pre f)
  | 0, pre, p, f, hp => by
    -- Base case: no quantifiers. `arithmetizeQBFAux 0 _ p = p`, and
    -- `valueAt 0 _ f = f Fin.elim0`. The hypothesis at the (unique) empty
    -- boolean assignment gives us exactly what we need.
    have : (fun i : Fin 0 => boolToField (Fin.elim0 i : Bool))
        = (Fin.elim0 : Fin 0 → 𝔽) := by funext i; exact i.elim0
    unfold arithmetizeQBFAux valueAt
    rw [← this]
    exact hp Fin.elim0
  | m + 1, pre, p, f, hp => by
    -- Recursive case. The two branches `specialize0 p 0` and `specialize0 p 1`
    -- encode `fun y => f (Fin.cons false y)` and `fun y => f (Fin.cons true y)`
    -- respectively (by `eval_specialize0`). Apply the IH to each branch, then
    -- combine via the quantifier's arithmetic identity.
    have hp0 : ∀ y : Fin m → Bool, (CMvPolynomial.specialize0 p 0).eval
        (fun i => boolToField (y i))
        = boolToField (f (Fin.cons false y)) := by
      intro y
      rw [CMvPolynomial.eval_specialize0]
      have eq :
          (Fin.cons (0 : 𝔽) (fun i => boolToField (y i)) : Fin (m + 1) → 𝔽)
          = (fun i => boolToField ((Fin.cons false y : Fin (m + 1) → Bool) i)) := by
        funext i
        cases i using Fin.cases <;> simp [Fin.cons, boolToField]
      rw [eq, hp]
    have hp1 : ∀ y : Fin m → Bool, (CMvPolynomial.specialize0 p 1).eval
        (fun i => boolToField (y i))
        = boolToField (f (Fin.cons true y)) := by
      intro y
      rw [CMvPolynomial.eval_specialize0]
      have eq :
          (Fin.cons (1 : 𝔽) (fun i => boolToField (y i)) : Fin (m + 1) → 𝔽)
          = (fun i => boolToField ((Fin.cons true y : Fin (m + 1) → Bool) i)) := by
        funext i
        cases i using Fin.cases <;> simp [Fin.cons, boolToField]
      rw [eq, hp]
    have ih0 := arithmetizeQBFAux_eval m (fun i => pre i.succ)
      (CMvPolynomial.specialize0 p 0) (fun y => f (Fin.cons false y)) hp0
    have ih1 := arithmetizeQBFAux_eval m (fun i => pre i.succ)
      (CMvPolynomial.specialize0 p 1) (fun y => f (Fin.cons true y)) hp1
    unfold arithmetizeQBFAux valueAt
    cases pre 0 with
    | «forall» =>
      rw [CPoly.eval_mul, ih0, ih1, ← boolToField_and]
    | «exists» =>
      rw [CPoly.eval_sub, CPoly.eval_mul, CPoly.eval_sub, CPoly.eval_sub,
          CPoly.eval_one, ih0, ih1, ← boolToField_or]

/-- **Main theorem.** The arithmetization of a TQBF formula, evaluated at the
empty assignment, equals `boolToField` of the formula's truth value. In
particular, it is `1` iff the formula is valid. -/
theorem arithmetizeQBF_eq_boolToField_value {n : ℕ} (Q : QBF n) :
    (arithmetizeQBF (𝔽 := 𝔽) Q).eval Fin.elim0 = boolToField Q.value := by
  unfold arithmetizeQBF QBF.value
  apply arithmetizeQBFAux_eval
  intro x
  rw [SharpSAT.eval_arithmetize_eq_indicator]
  cases Q.matrix.eval x <;> simp [boolToField]

end TQBF
