import CompPoly.CMvPolynomial
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation

@[simp]
def hypercube_n {𝔽} [CommSemiring 𝔽] [DecidableEq 𝔽] (n : ℕ) : Finset (Fin n → 𝔽) :=
  Fintype.piFinset (fun _ : Fin n => ({0, 1} : Finset 𝔽))

-- takes fixed vars set and returns set containing all extensions over cube size open_vars
@[simp] def boolean_extension {𝔽 : Type _} [CommRing 𝔽] [DecidableEq 𝔽]
  {num_fixed_vars : ℕ}
  (fixed : Fin num_fixed_vars → 𝔽)
  (num_open_vars : ℕ) : Finset (Fin (num_fixed_vars + num_open_vars) → 𝔽) :=
by
  classical
  let hypercube : Finset (Fin num_open_vars → 𝔽) :=
    hypercube_n (𝔽 := 𝔽) num_open_vars
  exact hypercube.image (fun x => Fin.addCases fixed x)

-- sum over open (num_vars - k) variables (after fixing the first k)
def residual_sum
  {𝔽 : Type} [CommRing 𝔽] [DecidableEq 𝔽]
  {k num_vars : ℕ}
  (ch : Fin k → 𝔽)
  (p : CPoly.CMvPolynomial num_vars 𝔽)
  (hk : k ≤ num_vars) : 𝔽 :=
by
  classical
  let openVars : ℕ := num_vars - k
  have hn : k + openVars = num_vars := by
    simpa [openVars] using (Nat.add_sub_of_le hk)
  let evaluation_points : Finset (Fin num_vars → 𝔽) := by
    simpa [openVars, hn] using
      (boolean_extension (𝔽 := 𝔽) (num_fixed_vars := k) ch openVars)
  exact ∑ point ∈ evaluation_points, CPoly.CMvPolynomial.eval point p

def round_sum
  {𝔽 : Type} [CommRing 𝔽] [DecidableEq 𝔽]
  {num_challenges num_vars : ℕ}
  (challenges : Fin num_challenges → 𝔽)
  (current : 𝔽)
  (p : CPoly.CMvPolynomial num_vars 𝔽)
  (hcard : num_challenges + 1 ≤ num_vars) : 𝔽 :=
by
  -- the same as residual sum after fixing the current variable
  exact residual_sum (𝔽 := 𝔽)
    (k := num_challenges + 1) (num_vars := num_vars)
    (ch := Fin.snoc challenges current)
    (p := p)
    (hk := hcard)

def true_sum
  {n : ℕ} {𝔽 : Type} [CommRing 𝔽] [DecidableEq 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽) : 𝔽 :=
by
  classical
  let empty : Fin 0 → 𝔽 := fun i => (Fin.elim0 i)
  exact residual_sum (𝔽 := 𝔽) (k := 0) (num_vars := n) empty p (by simp)

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
        Fin.cons b x
      exact add (ih (fun x => F (extend b0 x)))
                (ih (fun x => F (extend b1 x)))
