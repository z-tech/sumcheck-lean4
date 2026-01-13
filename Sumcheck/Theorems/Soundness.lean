import Sumcheck.Probability.Soundness

theorem soundness
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (claim : 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (adv : Adversary 𝔽 n)
  (hfalse : claim ≠ true_sum (𝔽 := 𝔽) p) :
  prob_soundness (𝔽 := 𝔽) (n := n) claim p adv
    ≤ n * (max_ind_degree p) / field_size := by
  -- proof will be: reduce to a bound on `prob_over_challenges` of Accepts ∧ Bad
  -- then apply your “Schwartz–Zippel / sumcheck soundness” lemma for Bad
  sorry
