import Sumcheck.Src.CMvPolynomial
import Sumcheck.Src.Hypercube

def honest_prover_message
  {𝔽} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  {n k : ℕ}
  (p : CPoly.CMvPolynomial n 𝔽)
  (challenges : Fin k → 𝔽)
  (hcard : k + 1 ≤ n) : CPoly.CMvPolynomial 1 𝔽 :=
by
  classical
  let num_open_vars : ℕ := n - (k + 1)
  have h_num_open_vars : (k + 1) + num_open_vars = n := by
    simpa [num_open_vars] using Nat.add_sub_of_le hcard
  have h_num_open_vars_rearranged : k + (num_open_vars + 1) = n := by
    calc
      k + (num_open_vars + 1) = k + num_open_vars + 1 := by simp [Nat.add_assoc]
      _ = k + 1 + num_open_vars := by
        simpa [Nat.add_assoc] using (Nat.add_right_comm k num_open_vars 1)
      _ = (k + 1) + num_open_vars := by simp [Nat.add_assoc]
      _ = n := h_num_open_vars

  let left_map : Fin k → CPoly.CMvPolynomial 1 𝔽 := fun i => c1 (challenges i)

  let right_map (b : Fin num_open_vars → 𝔽) : Fin (num_open_vars + 1) → CPoly.CMvPolynomial 1 𝔽 :=
    Fin.cons (n := num_open_vars)
      (α := fun _ : Fin (num_open_vars + 1) => CPoly.CMvPolynomial 1 𝔽)
      x0
      (fun j => c1 (b j))

  let combined_map (b : Fin num_open_vars → 𝔽) : Fin n → CPoly.CMvPolynomial 1 𝔽 :=
    append_variable_assignments (𝔽 := 𝔽) (k := k) (m := num_open_vars + 1) (n := n) h_num_open_vars_rearranged
      left_map (right_map b)

  exact sum_over_hypercube_recursive (β := CPoly.CMvPolynomial 1 𝔽)
    (b0 := 0) (b1 := 1)
    (add := fun a b => a + b)
    (m := num_open_vars)
    (F := fun b => CPoly.eval₂Poly c1 (combined_map b) p)
