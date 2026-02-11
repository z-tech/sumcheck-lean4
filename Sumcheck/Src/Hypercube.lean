import CompPoly.Multivariate.CMvPolynomial
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation

import Sumcheck.Src.CMvPolynomial

-- glue together the substitution functions left and right
def append_variable_assignments
  {𝔽 : Type _} [CommSemiring 𝔽]
  {k m n : ℕ}
  (hn : k + m = n)
  (left : Fin k → CPoly.CMvPolynomial 1 𝔽)
  (right : Fin m → CPoly.CMvPolynomial 1 𝔽) : Fin n → CPoly.CMvPolynomial 1 𝔽 :=
fun i =>
  Fin.addCases (m := k) (n := m) (motive := fun _ => CPoly.CMvPolynomial 1 𝔽)
    left right (Fin.cast hn.symm i)

/-- Sum a function `F` over all assignments from `domain^m`.
    Generalizes the boolean hypercube sum from `{0,1}^m` to an arbitrary finite domain.
    - `domain`: the finite set of values for each variable (as a list)
    - `add`: a binary operation to combine results (typically `(· + ·)`)
    - `zero`: the identity element for `add` (typically `0`)
    - `m`: the number of variables to sum over
    - `F`: the function to evaluate at each assignment -/
def sum_over_domain_recursive
  {𝔽 β : Type _}
  (domain : List 𝔽)
  (add : β → β → β) (zero : β)
  {m : ℕ}
  (F : (Fin m → 𝔽) → β) : β :=
by
  classical
  induction m with
  | zero =>
      exact F (fun i => nomatch i)
  | succ m ih =>
      let extend (a : 𝔽) (x : Fin m → 𝔽) : Fin (m+1) → 𝔽 :=
        fun i => Fin.cases a x i
      exact domain.foldl (fun acc a => add acc (ih (fun x => F (extend a x)))) zero

/-- Sum over the boolean hypercube {b0, b1}^m. Kept for backwards compatibility. -/
def sum_over_hypercube_recursive
  {𝔽 β : Type _}
  (b0 b1 : 𝔽)
  (add : β → β → β)
  {m : ℕ}
  (F : (Fin m → 𝔽) → β) : β :=
by
  classical
  induction m with
  | zero =>
      exact F (fun i => nomatch i)
  | succ m ih =>
      let extend (b : 𝔽) (x : Fin m → 𝔽) : Fin (m+1) → 𝔽 :=
        fun i => Fin.cases b x i
      exact add (ih (fun x => F (extend b0 x)))
                (ih (fun x => F (extend b1 x)))

/-- Non-dependent `Fin.addCases` specialized to functions. Avoids needing to specify `motive`. -/
def addCasesFun {α : Type} {m n : ℕ}
  (f : Fin m → α) (g : Fin n → α) : Fin (m + n) → α :=
fun i => Fin.addCases (m := m) (n := n) (motive := fun _ => α) f g i

def residual_sum
  {𝔽 : Type} [CommRing 𝔽] [DecidableEq 𝔽]
  {k num_vars : ℕ}
  (domain : List 𝔽)
  (ch : Fin k → 𝔽)
  (p : CPoly.CMvPolynomial num_vars 𝔽)
  (hk : k ≤ num_vars) : 𝔽 :=
by
  classical
  let openVars : ℕ := num_vars - k
  have hn : k + openVars = num_vars := by
    simpa [openVars] using Nat.add_sub_of_le hk
  exact
    sum_over_domain_recursive (𝔽 := 𝔽) (β := 𝔽)
      domain (· + ·) 0 (m := openVars)
      (fun x =>
        let point : Fin num_vars → 𝔽 :=
          fun i => addCasesFun ch x (Fin.cast hn.symm i)
        CPoly.CMvPolynomial.eval point p)

def residual_sum_with_openVars
  {𝔽 : Type} [CommRing 𝔽] [DecidableEq 𝔽]
  {k n : ℕ}
  (domain : List 𝔽)
  (openVars : ℕ)
  (hn : k + openVars = n)
  (ch : Fin k → 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽) : 𝔽 :=
  sum_over_domain_recursive (𝔽 := 𝔽) (β := 𝔽)
    domain (· + ·) 0 (m := openVars)
    (fun x =>
      let point : Fin n → 𝔽 := fun i => addCasesFun ch x (Fin.cast hn.symm i)
      CPoly.CMvPolynomial.eval point p)

def round_sum
  {𝔽 : Type} [CommRing 𝔽] [DecidableEq 𝔽]
  {num_challenges num_vars : ℕ}
  (domain : List 𝔽)
  (challenges : Fin num_challenges → 𝔽)
  (current : 𝔽)
  (p : CPoly.CMvPolynomial num_vars 𝔽)
  (hcard : num_challenges + 1 ≤ num_vars) : 𝔽 :=
by
  -- the same as residual sum after fixing the current variable
  exact residual_sum (𝔽 := 𝔽)
    domain
    (k := num_challenges + 1) (num_vars := num_vars)
    (ch := Fin.snoc challenges current)
    (p := p)
    (hk := hcard)

-- The claim the honest prover makes: the sum of p over domain^n
def honest_claim
  {n : ℕ} {𝔽 : Type} [CommRing 𝔽] [DecidableEq 𝔽]
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽) : 𝔽 :=
by
  classical
  let empty : Fin 0 → 𝔽 := fun i => (Fin.elim0 i)
  exact residual_sum (𝔽 := 𝔽) domain (k := 0) (num_vars := n) empty p (by simp)
