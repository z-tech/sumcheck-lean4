import Sumcheck.Src.CMvPolynomial
import Sumcheck.Src.Hypercube

-- number of open vars
def num_open_vars {n : ℕ} (i : Fin n) : ℕ :=
  n - (i.val + 1)

/-- Right-side map of length (open + 1): first is x0, rest are constants from b. -/
def honest_right_map
  {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  {n : ℕ} (i : Fin n)
  (b : Fin (num_open_vars (n := n) i) → 𝔽) :
    Fin (num_open_vars (n := n) i + 1) → CPoly.CMvPolynomial 1 𝔽
| ⟨0, _⟩ => x0
| ⟨j + 1, hj⟩ =>
    have hj' : j < num_open_vars (n := n) i := by
      exact Nat.lt_of_succ_lt_succ hj
    c1 (b ⟨j, hj'⟩)

/-- The combined substitution map Fin n → CMvPolynomial 1 𝔽 used by the honest prover
    at round i, for a particular hypercube assignment b. -/
def honest_combined_map
  {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  {n : ℕ} (i : Fin n)
  (challenges : Fin i.val → 𝔽)
  (b : Fin (num_open_vars (n := n) i) → 𝔽) :
    Fin n → CPoly.CMvPolynomial 1 𝔽 :=
  have hn : i.val + (num_open_vars (n := n) i + 1) = n := by
    set m : ℕ := num_open_vars (n := n) i
    have hle : i.val + 1 ≤ n := Nat.succ_le_of_lt i.isLt
    have h1 : (i.val + 1) + m = n := by
      simpa [m, num_open_vars] using (Nat.add_sub_of_le hle)
    calc
      i.val + (m + 1)
          = i.val + m + 1 := by simp [Nat.add_assoc]
      _   = i.val + 1 + m := by
              simpa [Nat.add_assoc] using (Nat.add_right_comm i.val m 1)
      _   = (i.val + 1) + m := by simp [Nat.add_assoc]
      _   = n := h1
  append_variable_assignments (𝔽 := 𝔽) (k := i.val) (m := num_open_vars (n := n) i + 1)
    (n := n) hn
    (left := fun j => c1 (challenges j))
    (right := honest_right_map (𝔽 := 𝔽) (n := n) i b)

/-- New lemma-friendly API: specify the round by i : Fin n directly. -/
def honest_prover_message_at
  {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  {n : ℕ}
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (i : Fin n)
  (challenges : Fin i.val → 𝔽) : CPoly.CMvPolynomial 1 𝔽 :=
  sum_over_domain_recursive (β := CPoly.CMvPolynomial 1 𝔽)
    domain
    (add := fun a b =>
      @HAdd.hAdd (CPoly.CMvPolynomial 1 𝔽) (CPoly.CMvPolynomial 1 𝔽) (CPoly.CMvPolynomial 1 𝔽)
        instHAdd a b)
    (zero := c1 (𝔽 := 𝔽) 0)
    (m := num_open_vars (n := n) i)
    (F := fun b =>
      CPoly.eval₂Poly c1 (honest_combined_map (𝔽 := 𝔽) (n := n) i challenges b) p)

/-- Backwards-compatible wrapper: keep the old signature so existing call sites compile. -/
def honest_prover_message
  {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  {n k : ℕ}
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (challenges : Fin k → 𝔽)
  (hcard : k + 1 ≤ n) : CPoly.CMvPolynomial 1 𝔽 :=
  honest_prover_message_at domain (p := p)
    (i := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hcard⟩)
    (challenges := challenges)
