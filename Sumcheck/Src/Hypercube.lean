import CompPoly.CMvPolynomial
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

lemma sum_over_hypercube_recursive_succ_def
  {𝔽 β : Type _}
  (b0 b1 : 𝔽)
  (add : β → β → β)
  (m : ℕ)
  (F : (Fin (m+1) → 𝔽) → β) :
  sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add (m := m+1) F
    =
    add
      (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add (m := m)
        (fun x => F (Fin.cons b0 x)))
      (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add (m := m)
        (fun x => F (Fin.cons b1 x))) := by
  -- This works because your definition is literally recursion on m.
  -- `simp` reduces the succ-case definitionally.
  simp [sum_over_hypercube_recursive]


@[simp] lemma sum_over_hypercube_recursive_succ
  {𝔽 β : Type _}
  (b0 b1 : 𝔽)
  (add : β → β → β)
  {m : ℕ}
  (F : (Fin (Nat.succ m) → 𝔽) → β) :
  sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add (m := Nat.succ m) F
    =
    add
      (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add (m := m)
        (fun x => F (Fin.cons b0 x)))
      (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add (m := m)
        (fun x => F (Fin.cons b1 x))) := by
  -- definitional reduction: your `sum_over_hypercube_recursive` is literally an `induction m`
  simp [sum_over_hypercube_recursive]

@[simp] lemma sum_over_hypercube_recursive_succ'
  {𝔽 β : Type _}
  (b0 b1 : 𝔽)
  (add : β → β → β)
  {m : ℕ}
  (F : (Fin (m+1) → 𝔽) → β) :
  sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add (m := m+1) F
    =
    add
      (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add (m := m)
        (fun x => F (Fin.cons b0 x)))
      (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add (m := m)
        (fun x => F (Fin.cons b1 x))) := by
  simp [sum_over_hypercube_recursive]

lemma sum_over_hypercube_recursive_deg_le
  {𝔽 β : Type _}
  (deg : β → ℕ) (d : ℕ)
  (b0 b1 : 𝔽)
  (add : β → β → β)
  {m : ℕ}
  (F : (Fin m → 𝔽) → β)
  (hadd : ∀ a b, deg a ≤ d → deg b ≤ d → deg (add a b) ≤ d)
  (hF : ∀ x, deg (F x) ≤ d) :
  deg (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add (m := m) F) ≤ d := by
  classical
  induction m with
  | zero =>
      -- only one assignment exists: Fin 0 → 𝔽
      simpa [sum_over_hypercube_recursive] using hF (fun i => nomatch i)
  | succ m ih =>
      -- split on the last coordinate (0 vs 1)
      have h0 :
          deg
            (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add (m := m)
              (fun x => F (Fin.cons b0 x))) ≤ d :=
        ih (F := fun x => F (Fin.cons b0 x))
           (hF := fun x => hF (Fin.cons b0 x))
      have h1 :
          deg
            (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add (m := m)
              (fun x => F (Fin.cons b1 x))) ≤ d :=
        ih (F := fun x => F (Fin.cons b1 x))
           (hF := fun x => hF (Fin.cons b1 x))
      -- now combine the two branches using hadd
      simpa [sum_over_hypercube_recursive_succ (𝔽 := 𝔽) (β := β) b0 b1 add (m := m) (F := F)]
        using hadd
          (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add (m := m) (fun x => F (Fin.cons b0 x)))
          (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 add (m := m) (fun x => F (Fin.cons b1 x)))
          h0 h1

lemma sum_over_hypercube_recursive_map
  {𝔽 β γ : Type _}
  (b0 b1 : 𝔽)
  (addβ : β → β → β)
  (addγ : γ → γ → γ)
  (g : β → γ)
  (hg : ∀ a b, g (addβ a b) = addγ (g a) (g b))
  {m : ℕ}
  (F : (Fin m → 𝔽) → β) :
  g (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 addβ (m := m) F)
    =
  sum_over_hypercube_recursive (𝔽 := 𝔽) (β := γ) b0 b1 addγ (m := m) (fun x => g (F x)) := by
  classical
  induction m with
  | zero =>
      simp [sum_over_hypercube_recursive]
  | succ m ih =>
      -- Apply IH to the two branch functions explicitly
      have ih0 :
          g (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 addβ (m := m)
                (fun x => F (Fin.cons b0 x)))
            =
          sum_over_hypercube_recursive (𝔽 := 𝔽) (β := γ) b0 b1 addγ (m := m)
                (fun x => g (F (Fin.cons b0 x))) :=
        ih (F := fun x => F (Fin.cons b0 x))

      have ih1 :
          g (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := β) b0 b1 addβ (m := m)
                (fun x => F (Fin.cons b1 x)))
            =
          sum_over_hypercube_recursive (𝔽 := 𝔽) (β := γ) b0 b1 addγ (m := m)
                (fun x => g (F (Fin.cons b1 x))) :=
        ih (F := fun x => F (Fin.cons b1 x))

      -- IMPORTANT: rewrite both sides using the *succ lemma*, not the definition (avoids Nat.recAux junk)
      -- LHS becomes g (addβ (...) (...)), RHS becomes addγ (...) (...)
      simp [sum_over_hypercube_recursive_succ, hg, ih0, ih1]


/-- `eval₂` commutes with `sum_over_hypercube_recursive` when `add` is `+`. -/
lemma eval₂_sum_over_hypercube_recursive
  {𝔽 : Type _} {m : ℕ}
  [CommSemiring 𝔽] [DecidableEq 𝔽]
  (b0 b1 : 𝔽)
  (vs : Fin 1 → 𝔽)
  (F : (Fin m → 𝔽) → CPoly.CMvPolynomial 1 𝔽) :
  CPoly.CMvPolynomial.eval₂ (R := 𝔽) (S := 𝔽) (n := 1) (RingHom.id 𝔽) vs
      (sum_over_hypercube_recursive (𝔽 := 𝔽) (β := CPoly.CMvPolynomial 1 𝔽)
        b0 b1 (fun a b => a + b) (m := m) F)
    =
  sum_over_hypercube_recursive (𝔽 := 𝔽) (β := 𝔽)
    b0 b1 (fun a b => a + b) (m := m)
    (fun x =>
      CPoly.CMvPolynomial.eval₂ (R := 𝔽) (S := 𝔽) (n := 1) (RingHom.id 𝔽) vs (F x)) := by
  classical
  -- use the generic "map" lemma with g = eval₂
  refine
    (sum_over_hypercube_recursive_map
      (𝔽 := 𝔽) (β := CPoly.CMvPolynomial 1 𝔽) (γ := 𝔽)
      (b0 := b0) (b1 := b1)
      (addβ := fun a b => a + b)
      (addγ := fun a b => a + b)
      (g := fun p =>
        CPoly.CMvPolynomial.eval₂ (R := 𝔽) (S := 𝔽) (n := 1) (RingHom.id 𝔽) vs p)
      (hg := ?_)
      (m := m)
      (F := F))
  intro a b
  -- `eval₂` is a ring hom in the polynomial argument, so it preserves addition.
  -- This simp lemma name varies; one of these usually exists:
  --   `CPoly.CMvPolynomial.eval₂_add`, or `map_add`, or simp can do it after unfolding.
  simpa using (CPoly.CMvPolynomial.eval₂_add
    (R := 𝔽) (S := 𝔽) (n := 1) (f := (RingHom.id 𝔽)) (vs := vs) a b)

/-- Non-dependent `Fin.addCases` specialized to functions. Avoids needing to specify `motive`. -/
def addCasesFun {α : Type} {m n : ℕ}
  (f : Fin m → α) (g : Fin n → α) : Fin (m + n) → α :=
fun i => Fin.addCases (m := m) (n := n) (motive := fun _ => α) f g i

@[simp] lemma addCasesFun_apply {α} {m n} (f : Fin m → α) (g : Fin n → α) (i : Fin (m+n)) :
  addCasesFun f g i = Fin.addCases (m:=m) (n:=n) (motive := fun _ => α) f g i := rfl

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
    simpa [openVars] using Nat.add_sub_of_le hk
  exact
    sum_over_hypercube_recursive (𝔽 := 𝔽) (β := 𝔽)
      (0 : 𝔽) (1 : 𝔽) (· + ·) (m := openVars)
      (fun x =>
        let point : Fin num_vars → 𝔽 :=
          fun i => addCasesFun ch x (Fin.cast hn.symm i)
        CPoly.CMvPolynomial.eval point p)

def residual_sum_with_openVars
  {𝔽 : Type} [CommRing 𝔽] [DecidableEq 𝔽]
  {k n : ℕ}
  (openVars : ℕ)
  (hn : k + openVars = n)
  (ch : Fin k → 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽) : 𝔽 :=
  sum_over_hypercube_recursive (𝔽 := 𝔽) (β := 𝔽)
    (0 : 𝔽) (1 : 𝔽) (· + ·) (m := openVars)
    (fun x =>
      let point : Fin n → 𝔽 := fun i => addCasesFun ch x (Fin.cast hn.symm i)
      CPoly.CMvPolynomial.eval point p)

lemma residual_sum_eq_with_openVars_def
  {𝔽 : Type} [CommRing 𝔽] [DecidableEq 𝔽]
  {k n : ℕ} (ch : Fin k → 𝔽) (p : CPoly.CMvPolynomial n 𝔽) (hk : k ≤ n) :
  residual_sum (𝔽 := 𝔽) (k := k) (num_vars := n) ch p hk
    =
  residual_sum_with_openVars (𝔽 := 𝔽) (k := k) (n := n)
    (openVars := n - k) (hn := by simpa using Nat.add_sub_of_le hk) ch p := by
  classical
  unfold residual_sum residual_sum_with_openVars
  simp (config := { zeta := true })

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
