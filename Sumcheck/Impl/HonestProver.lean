import CompPoly.Lawful
import CompPoly.CMvMonomial
import CompPoly.CMvPolynomial
import Mathlib.Data.ZMod.Basic

import Sumcheck.Impl.Polynomials

def honest_prover_message
  {𝔽} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  {n k : ℕ}
  (p : CPoly.CMvPolynomial n 𝔽)
  (challenges : Fin k → 𝔽)
  (hcard : k + 1 ≤ n) : CPoly.CMvPolynomial 1 𝔽 :=
by
  classical
  let openVars : ℕ := n - (k + 1)

  have hn : (k + 1) + openVars = n := by
    simpa [openVars] using Nat.add_sub_of_le hcard

  have hn' : k + (openVars + 1) = n := by
    calc
      k + (openVars + 1) = k + openVars + 1 := by simp [Nat.add_assoc]
      _ = k + 1 + openVars := by
        simpa [Nat.add_assoc] using (Nat.add_right_comm k openVars 1)
      _ = (k + 1) + openVars := by simp [Nat.add_assoc]
      _ = n := hn

  let C1 : 𝔽 → CPoly.CMvPolynomial 1 𝔽 := fun c => c1 (𝔽 := 𝔽) c
  let X  : CPoly.CMvPolynomial 1 𝔽 := x0 (𝔽 := 𝔽)

  let leftMap : Fin k → CPoly.CMvPolynomial 1 𝔽 :=
    fun i => C1 (challenges i)

  let rightMap (b : Fin openVars → 𝔽) : Fin (openVars + 1) → CPoly.CMvPolynomial 1 𝔽 :=
    Fin.cons (n := openVars)
      (α := fun _ : Fin (openVars + 1) => CPoly.CMvPolynomial 1 𝔽)
      X
      (fun j => C1 (b j))

  let varMap (b : Fin openVars → 𝔽) : Fin n → CPoly.CMvPolynomial 1 𝔽 :=
    addCasesCastPoly (𝔽 := 𝔽) (k := k) (m := openVars + 1) (n := n) hn'
      leftMap (rightMap b)

  -- AFP-style: q(X) = Σ_{b ∈ {0,1}^{openVars}} inst(p, b)
  exact cubeSum01 (𝔽 := 𝔽) (β := CPoly.CMvPolynomial 1 𝔽)
    -- use *your* notion of 0/1 for the Boolean hypercube:
    (b0 := (0 : 𝔽)) (b1 := (1 : 𝔽))  -- if numerals work
    (add := fun a b => a + b)
    (m := openVars)
    (F := fun b => CPoly.eval₂Poly (𝔽 := 𝔽) C1 (varMap b) p)
