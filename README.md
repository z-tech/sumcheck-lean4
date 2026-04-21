# Sumcheck-Lean4

The **Sumcheck protocol** written in [Lean 4](https://lean-lang.org/) using [`CMvPolynomial`](https://github.com/Verified-zkEVM/CompPoly).

## Key Features

- **Fully Computable**: Transcript generation is provided given a [`CMvPolynomial`](https://github.com/Verified-zkEVM/CompPoly), a claim, and challenge set.
- **Formalized Theorems**: Notions of `completeness` and `soundness` are machine-checked.

## Theorems

### Completeness

> If the prover is honest, the verifier always accepts.

```
theorem perfect_completeness
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽) :
  prob_over_challenges
    (fun r => AcceptsEvent p (generate_honest_transcript p (honest_claim p) r))
  = 1
```

Given a multivariate polynomial $p : \mathbb{F}[X_1, \dots, X_n]$ and an honest prover who sets:

$$c_0 = \sum_{b \in \\{0,1\\}^n} p(b)$$

the verifier accepts with probability exactly 1 over all challenge tuples $r \in \mathbb{F}^n$.

### Soundness

> If the claim is false, the verifier accepts with low probability.

```
theorem soundness_dishonest
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (claim : 𝔽)
  (claim_p : CPoly.CMvPolynomial n 𝔽)
  (adv : Adversary 𝔽 n)
  (h : claim ≠ honest_claim (p := claim_p)) :
  prob_over_challenges (E := AcceptsOnChallenges claim claim_p adv)
    ≤ n * (max_ind_degree claim_p) / field_size
```

If a prover claims a value $c \neq \sum_{b \in \\{0,1\\}^n} p(b)$, then for any strategy, the probability the verifier accepts is bounded by:

$$\Pr[\text{accept}] \leq \frac{n \cdot d}{|\mathbb{F}|}$$

where $d = \max_i \deg_{X_i}(p)$ is the max individual degree of $p$. The proof sketch is:

1. **Reduction**: a dishonest claim implies at least one "bad" round where the prover's polynomial $\neq$ honest one.
2. **Union bound**: the acceptance probability is bounded by the sum over rounds.
3. **Schwartz–Zippel**: at each bad round, the probability of the verifier's random challenge hitting a root of the difference polynomial is at most $d / |\mathbb{F}|$ (via Mathlib's `MvPolynomial.schwartz_zippel_sum_degreeOf`).

## Applications

Results built on top of the core sumcheck protocol:

- **`#SAT ∈ IP`** ([Sumcheck/IP/SharpSAT/](Sumcheck/IP/SharpSAT/)) — proved
  unconditionally. 3-CNF arithmetization, `sharpSAT_completeness`,
  `sharpSAT_soundness`, concrete `sharpSAT_soundnessError_le` bound, and
  `sharpSAT_inIPFamily_concrete` packaging bounded-size instances into
  the size-indexed `InIPFamily` complexity class (field scheme:
  `ZMod p_k` for primes discharging the field hypotheses).
- **Inner-product sumcheck** ([Sumcheck/IP/InnerProduct.lean](Sumcheck/IP/InnerProduct.lean)) —
  `InnerProductStatement` claiming `c = Σ f(x)·g(x)` over a boolean
  hypercube (or other domain), reduced to sumcheck on `f * g`.
  Completeness, soundness, and a multilinear soundness-error bound of
  `n · 2 / |𝔽|`.
- **TQBF / Shamir's theorem** ([Sumcheck/IP/TQBF/](Sumcheck/IP/TQBF/)) —
  scaffolding in progress. QBF arithmetization, multilinear-extension
  library (`linearize0`, `linearizeAll` with degree bounds), Shamir
  protocol definition, key algebraic identities (`specialize0_commute`,
  `eval_arithmetizeLeavingFirst`). `tqbf_inIP` still open pending a
  `tqbfHonestMessage` cast refactor.
- **IP complexity class** ([InteractiveProtocol/Properties/IPClass.lean](InteractiveProtocol/Properties/IPClass.lean)) —
  `InIP` and size-indexed `InIPFamily` with smart constructors
  (`of_hasProperties`) for packaging any protocol that has been proved
  complete + sound into the corresponding language-membership claim.

## Honest Prover

The honest prover message at round $i$ is defined as the **univariate polynomial** in $X_i$ computed by summing out the remaining variables over the Boolean hypercube:

$$g_i(X_i) = \sum_{b \in \\{0,1\\}^{n-i-1}} p(r_1, \dots, r_{i-1}, X_i, b_1, \dots, b_{n-i-1})$$

where $r_1, \dots, r_{i-1}$ are the verifier's previous challenges. This is implemented in [`Src/Prover.lean`](Sumcheck/Src/Prover.lean) as `honest_prover_message_at`, which:

1. Builds a **substitution map** `Fin n → CMvPolynomial 1 𝔽` that replaces the first $i$ variables with constants (the challenges), the $(i{+}1)$-th variable with the indeterminate $X_0$, and the remaining variables with hypercube bits.
2. Evaluates $p$ under this substitution via `eval₂Poly`, producing a univariate polynomial.
3. **Sums** these univariates over all $\\{0,1\\}^{n-i-1}$ assignments using `sum_over_hypercube_recursive`.

## License

This project is released under the **Apache License 2.0**. See [LICENSE](LICENSE) for details.