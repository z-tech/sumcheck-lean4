import Sumcheck.IP.TQBF.QBF
import Sumcheck.IP.TQBF.Arithmetize
import Sumcheck.IP.TQBF.Linearize
import Sumcheck.IP.InteractiveProtocol
import Sumcheck.Src.Transcript
import InteractiveProtocol.Properties.IPClass

/-!
# Shamir's theorem: TQBF ∈ IP

This file is the landing site for Shamir's theorem (and, via PSPACE-
completeness of TQBF, `PSPACE ⊆ IP` as the downstream corollary).

The polynomial infrastructure is all in place:
* **Arithmetization** (`arithmetizeQBF`) — produces a `CMvPolynomial 0 𝔽`
  that evaluates to `boolToField Q.value` (`arithmetizeQBF_eq_boolToField_value`).
* **Multilinear extension** (`linearizeAll`) — preserves boolean-cube
  evaluation (`eval_linearizeAll_boolean`) and produces a polynomial with
  individual degree at most 1 in every variable
  (`degreeOf_linearizeAll_le_one`).
* **Partial evaluation** (`specialize0`) with a correctness theorem
  (`eval_specialize0`) relating it to the original polynomial at the
  extended point.

What's left is the protocol construction and its completeness/soundness
proofs.

## Plan

The statement type bundles the data the verifier needs to know at the start
of the protocol: the quantifier prefix, the 3-CNF matrix, and the claimed
value (a field element, supposed to equal `boolToField Q.value`).

### Protocol sketch

At each round `i` (processing quantifier `Q_i`):
1. The prover has partially-evaluated the polynomial at challenges
   `r_1, …, r_{i-1}`. The current claim is `c_i ∈ 𝔽`, which the prover
   asserts equals the value at the current state.
2. The prover sends a univariate polynomial `g_i(X) : 𝔽[X]` that is supposed
   to be the polynomial seen as a function of the `i`-th variable only
   (with the preceding challenges substituted and the remaining quantifiers
   folded in).
3. The verifier checks:
   - **∀** case: `g_i(0) · g_i(1) = c_i` (product check).
   - **∃** case: `1 - (1 - g_i(0)) · (1 - g_i(1)) = c_i`.
4. The verifier samples a uniform random challenge `r_i ∈ 𝔽` and updates
   the claim to `c_{i+1} := g_i(r_i)`.

After all `n` rounds, the verifier has a claim about a fully-evaluated
polynomial at `(r_1, …, r_n)`. She evaluates the (multilinearized)
arithmetization directly and checks against the final claim.

### Completeness

The honest prover sends `g_i(X)` = the correct univariate polynomial. By
construction, `g_i(0) · g_i(1) = c_i` (∀) or `1 - (1 - g_i(0))(1 - g_i(1))
= c_i` (∃). Each round's claim update matches the honest polynomial's
evaluation. Perfect completeness follows.

### Soundness

For any prover and invalid input, at each round, the sent polynomial
either matches the true underlying polynomial (in which case the check
fails) or differs. If it differs, by Schwartz–Zippel over a field of size
`|𝔽|`, the probability that a uniform `r_i` produces the same evaluation
is at most `d / |𝔽|`, where `d` is an upper bound on the polynomial's
degree. Using multilinearization (so each `g_i` has degree at most `1`),
soundness error at each round is `1 / |𝔽|`. By union bound over `n`
rounds: total soundness error `≤ n / |𝔽|`.

For `ε ≤ 1/3`, need `|𝔽| ≥ 3n`.

## Design trade-off: raw polynomials, exponential field size

The protocol here does **not** use intermediate linearization between
quantifier folds. This keeps the completeness argument clean — the honest
prover's round polynomials are exactly the "raw folds" and the verifier's
quantifier-combinator check matches by direct arithmetic. The price is
exponential degree in the round polynomials (up to `2^{n-i-1}` at round
`i`), which pushes the required field size to `|𝔽| ≥ 3·2^n` for the
standard `ε ≤ 1/3` IP soundness bound.

Critically, this is still **classical-IP compatible**: field elements are
`O(n)` bits (since the field order is bounded by `2^{O(n)}`), so the
verifier remains polynomial-time. The alternative — Shamir's original
linearization structure — keeps round polynomials multilinear at the cost
of ~`O(n²)` rounds with per-variable linearization operators. Either is
valid; this file takes the simpler route.

An earlier draft tried to combine linearized round polynomials with a
product-check verifier, which silently failed completeness: the
quantifier combinator of Boolean-point evaluations gives the *raw* fold
value, but the updated claim carries the *linearized* value from the
previous round, and these diverge off the Boolean cube. The current
design avoids the mismatch by keeping raw polynomials throughout.

## TODO

* ~~`TQBFStatement` structure (statement type).~~ ✓
* ~~`tqbfProtocol` — `PublicCoinProtocol TQBFStatement 𝔽 n` instantiation.~~
  ✓ (current simpler design, no linearization, no degree check)
* ~~`tqbfHonestProver` — the honest prover definition.~~ ✓
* `tqbf_hasPerfectCompleteness` — completeness proof. Remaining sub-lemmas:
  - ~~`specialize0_commute`~~ ✓ (in `Linearize.lean`, via `aeval` approach
    using `comp_aeval_apply` and `aeval_rename` after bridging through
    `fromCMvPolynomial_specialize0` and a new `finSuccEquiv_eval_C_eq_aeval`).
  - ~~`eval_arithmetizeLeavingFirst`~~ ✓ (below, by induction on `m`;
    inductive step uses `specialize0_commute`).
  - Honest-round-quantifier-check identity at each round. **Blocker:** the
    current `tqbfHonestMessage` uses `hn.symm ▸` / `hm ▸` casts to bridge
    arities (`(n - i.val) + i.val = n`, etc.). Reasoning through these
    casts is painful. A refactor that threads the arities more cleanly
    (e.g. via an index-shift helper or a dependently-typed signature) will
    make the proofs much smaller. Consider before proceeding.
  - Honest-final-check identity: `last claim = (arithmetize matrix).eval
    challenges`. Same cast issue.
* `tqbf_hasSoundnessError` — soundness proof. Schwartz-Zippel union bound
  over rounds: if any round's polynomial differs from the true one, a uniform
  random challenge distinguishes them with probability `≥ 1 - d_i / |𝔽|`
  where `d_i ≤ 2^{n-i-1}`. Total bound `≤ 2^n / |𝔽|`, making
  `|𝔽| ≥ 3·2^n` the natural field-size hypothesis.
* `tqbf_inIP` — package into `InIP` via `InIP.of_hasProperties`.
-/

namespace TQBF

open CPoly SharpSAT

/-- A TQBF statement bundles the quantifier prefix, the 3-CNF matrix, and
the claimed value of the arithmetization. The claim is a field element;
for a valid instance with the canonical encoding, it equals `1` (the field
embedding of `true`). -/
structure TQBFStatement (𝔽 : Type) [Field 𝔽] (n : ℕ) where
  quantifiers : Fin n → Quantifier
  matrix : CNF3 n
  claim : 𝔽

namespace TQBFStatement

variable {𝔽 : Type} [Field 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]

/-- The underlying QBF from a statement. -/
def toQBF {n : ℕ} (st : TQBFStatement 𝔽 n) : QBF n :=
  { quantifiers := st.quantifiers, matrix := st.matrix }

/-- A statement is correct when its claim equals `boolToField` of the
underlying QBF's value. -/
def Valid {n : ℕ} (st : TQBFStatement 𝔽 n) : Prop :=
  st.claim = SharpSAT.boolToField (𝔽 := 𝔽) st.toQBF.value

end TQBFStatement

/-- Canonical encoding of a QBF into a statement: use `claim = 1`, so that
`TQBFStatement.Valid` of the encoded statement is equivalent to `QBF.Valid`. -/
def QBF.toStatement {𝔽 : Type} [Field 𝔽] {n : ℕ} (Q : QBF n) :
    TQBFStatement 𝔽 n :=
  { quantifiers := Q.quantifiers, matrix := Q.matrix, claim := 1 }

section Correspondence

variable {𝔽 : Type} [Field 𝔽]

/-- Encoding preserves the language: a QBF is valid iff its encoded
statement is valid. -/
theorem qbf_valid_iff_toStatement_valid {n : ℕ} (Q : QBF n) :
    Q.Valid ↔ (Q.toStatement : TQBFStatement 𝔽 n).Valid := by
  unfold QBF.Valid TQBFStatement.Valid QBF.toStatement TQBFStatement.toQBF
  simp only
  cases Q.value <;> simp [SharpSAT.boolToField]

end Correspondence

/-! ### Helpers: iterated partial evaluation -/

namespace CMvPolynomial

variable {𝔽 : Type} [Field 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]

/-- Specialize the first `j` variables of a `(k + j)`-variable polynomial at
the given challenges, leaving the first `k` variables symbolic.

The arity `k + j` is chosen so that `k + (j + 1) = (k + j) + 1` reduces
definitionally (Nat.add's second-arg recursion), letting `specialize0` apply
without casts in the recursive step. -/
noncomputable def specializeFirst {k : ℕ} : ∀ (j : ℕ),
    (Fin j → 𝔽) → CPoly.CMvPolynomial (k + j) 𝔽 → CPoly.CMvPolynomial k 𝔽
  | 0, _, p => p
  | j + 1, chs, p =>
    specializeFirst j (fun i => chs i.succ)
      (CPoly.CMvPolynomial.specialize0 p (chs 0))

/-- `specialize0` preserves multilinearity. -/
theorem degreeOf_specialize0_le_one {n : ℕ} (p : CPoly.CMvPolynomial (n + 1) 𝔽)
    (c : 𝔽)
    (hp : ∀ i : Fin (n + 1), p.degreeOf i ≤ 1) :
    ∀ j : Fin n, (CPoly.CMvPolynomial.specialize0 p c).degreeOf j ≤ 1 :=
  fun j => le_trans (CPoly.CMvPolynomial.degreeOf_specialize0_succ_le p c j)
    (hp j.succ)

/-- `specializeFirst` preserves multilinearity. -/
theorem degreeOf_specializeFirst_le_one {k : ℕ} :
    ∀ (j : ℕ) (chs : Fin j → 𝔽) (p : CPoly.CMvPolynomial (k + j) 𝔽),
    (∀ i, p.degreeOf i ≤ 1) →
    ∀ κ : Fin k, (specializeFirst j chs p).degreeOf κ ≤ 1
  | 0, _, _, hp, κ => hp κ
  | j + 1, chs, p, hp, κ => by
    apply degreeOf_specializeFirst_le_one j (fun i => chs i.succ)
    intro i
    exact degreeOf_specialize0_le_one p (chs 0) hp i

end CMvPolynomial

/-! ### Helpers: partial arithmetization leaving one variable symbolic -/

section LeavingFirst

variable {𝔽 : Type} [Field 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]

/-- Fold the given quantifiers (corresponding to variables `1..m` of the input
polynomial) over a polynomial in `m + 1` variables, leaving variable 0
symbolic. Variables `1..m` get specialized at 0 and 1 in the standard
quantifier-elimination pattern.

**No intermediate linearization.** Unlike Shamir's original protocol, we
don't linearize between quantifier folds. This keeps the definition clean
and the completeness proof straightforward, at the cost of exponential
polynomial degree in the round messages — the honest prover's round-`i`
polynomial has degree up to `2^{n-i-1}`. Soundness then requires a field
of size `≥ 3 · 2^n` for `ε ≤ 1/3`. Elements of such a field are still
poly-many bits (`O(n)`), so the verifier remains polynomial-time. -/
noncomputable def arithmetizeLeavingFirst : ∀ {m : ℕ},
    (Fin m → Quantifier) → CPoly.CMvPolynomial (m + 1) 𝔽 →
      CPoly.CMvPolynomial 1 𝔽
  | 0, _, p => p
  | m + 1, qs, p =>
    let swap01 : Fin (m + 2) ≃ Fin (m + 2) := Equiv.swap 0 1
    let p_swap : CPoly.CMvPolynomial (m + 2) 𝔽 :=
      CPoly.CMvPolynomial.rename swap01 p
    let A0 : CPoly.CMvPolynomial 1 𝔽 :=
      arithmetizeLeavingFirst (fun i => qs i.succ)
        (CPoly.CMvPolynomial.specialize0 p_swap 0)
    let A1 : CPoly.CMvPolynomial 1 𝔽 :=
      arithmetizeLeavingFirst (fun i => qs i.succ)
        (CPoly.CMvPolynomial.specialize0 p_swap 1)
    match qs 0 with
    | .«forall» => A0 * A1
    | .«exists» => 1 - (1 - A0) * (1 - A1)

/-- **`arithmetizeLeavingFirst` collapses to `arithmetizeQBFAux` on scalar
inputs.** Evaluating the "leave-the-first-variable-symbolic" arithmetization at
a concrete value `c` agrees with first specializing the polynomial at `c` and
then folding all quantifiers via the standard recursive arithmetization. -/
theorem eval_arithmetizeLeavingFirst :
    ∀ {m : ℕ} (qs : Fin m → Quantifier)
      (p : CPoly.CMvPolynomial (m + 1) 𝔽) (c : 𝔽),
      (arithmetizeLeavingFirst qs p).eval (fun _ => c)
        = (arithmetizeQBFAux m qs
            (CPoly.CMvPolynomial.specialize0 p c)).eval Fin.elim0
  | 0, _, p, c => by
    show p.eval (fun _ => c)
      = (CPoly.CMvPolynomial.specialize0 p c).eval Fin.elim0
    rw [CPoly.CMvPolynomial.eval_specialize0]
    congr 1
    funext i
    match i with
    | ⟨0, _⟩ => rfl
  | m + 1, qs, p, c => by
    have ih0 := eval_arithmetizeLeavingFirst (fun i => qs i.succ)
      (CPoly.CMvPolynomial.specialize0
        (CPoly.CMvPolynomial.rename (Equiv.swap (0 : Fin (m + 2)) 1) p) 0) c
    have ih1 := eval_arithmetizeLeavingFirst (fun i => qs i.succ)
      (CPoly.CMvPolynomial.specialize0
        (CPoly.CMvPolynomial.rename (Equiv.swap (0 : Fin (m + 2)) 1) p) 1) c
    rw [CPoly.CMvPolynomial.specialize0_commute] at ih0 ih1
    unfold arithmetizeLeavingFirst arithmetizeQBFAux
    cases qs 0 with
    | «forall» =>
      rw [CPoly.eval_mul, CPoly.eval_mul, ih0, ih1]
    | «exists» =>
      rw [CPoly.eval_sub, CPoly.eval_sub, CPoly.eval_one, CPoly.eval_mul,
          CPoly.eval_sub, CPoly.eval_one, CPoly.eval_sub, CPoly.eval_one,
          CPoly.eval_mul, CPoly.eval_sub, CPoly.eval_one, CPoly.eval_sub,
          CPoly.eval_one, ih0, ih1]

end LeavingFirst

/-! ### Protocol construction -/

section Protocol

variable {𝔽 : Type} [Field 𝔽] [BEq 𝔽] [LawfulBEq 𝔽] [DecidableEq 𝔽]

/-- The per-round verifier check. Given a quantifier `q`, a current claim `c`,
and the prover's univariate round polynomial `g`, check:
* **∀**: `g(0) · g(1) = c` (product check).
* **∃**: `1 - (1 - g(0)) · (1 - g(1)) = c`.

Since we don't linearize between rounds, no degree bound is enforced at the
verifier level. Soundness is controlled by the field size instead. -/
@[simp] def tqbfVerifierRoundCheck
    (q : Quantifier) (claim : 𝔽) (roundP : CMvPolynomial 1 𝔽) : Bool :=
  let v0 : 𝔽 := CMvPolynomial.eval (fun _ => 0) roundP
  let v1 : 𝔽 := CMvPolynomial.eval (fun _ => 1) roundP
  let expected : 𝔽 := match q with
    | Quantifier.«forall» => v0 * v1
    | Quantifier.«exists» => 1 - (1 - v0) * (1 - v1)
  decide (expected = claim)

/-- Full verifier decision: every round-check passes, claim chain is
consistent, and the final claim matches the (raw) arithmetized matrix
evaluated at the random challenges. -/
noncomputable def isTqbfVerifierAccepts
    [Fintype 𝔽] {n : ℕ} (st : TQBFStatement 𝔽 n) (t : Transcript 𝔽 n) :
    Bool :=
  let claims := t.claims st.claim
  let matrixPoly : CMvPolynomial n 𝔽 := SharpSAT.arithmetize st.matrix
  let roundsOk : Bool :=
    (List.finRange n).all (fun i : Fin n =>
      tqbfVerifierRoundCheck (st.quantifiers i)
        (claims (Fin.castSucc i)) (t.roundPolys i)
      && decide (claims i.succ = nextClaim (t.challenges i) (t.roundPolys i)))
  let finalOk : Bool :=
    decide (claims (Fin.last n) = CMvPolynomial.eval t.challenges matrixPoly)
  roundsOk && finalOk

/-- The Shamir public-coin protocol for TQBF. `n` rounds (one per quantifier),
each sending a univariate polynomial in the current variable. Challenges are
uniform field elements. -/
noncomputable def tqbfProtocol [Fintype 𝔽] {n : ℕ} :
    PublicCoinProtocol (TQBFStatement 𝔽 n) 𝔽 n where
  ProverMessage := fun _ => CMvPolynomial 1 𝔽
  Transcript := (Fin n → CMvPolynomial 1 𝔽) × (Fin n → 𝔽)
  mkTranscript := fun msgs chs => (msgs, chs)
  challenges := fun tr => tr.2
  proverMessage := fun tr i => tr.1 i
  verifierAccepts := fun st tr =>
    isTqbfVerifierAccepts st
      { roundPolys := tr.1, challenges := tr.2 } = true
  verifierDecides := fun _ _ => inferInstance
  challenges_mk := fun _ _ => rfl
  proverMessage_mk := fun _ _ _ => rfl

end Protocol

/-! ### Honest prover -/

section HonestProver

variable {𝔽 : Type} [Field 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]

/-- Honest round message: at round `i` with prior challenges `chs`, return
the univariate polynomial representing the (raw) arithmetized matrix,
with `X_0, …, X_{i-1}` substituted by the challenges, `X_i` symbolic, and
remaining quantifiers `Q_{i+1}, …, Q_{n-1}` folded in. -/
noncomputable def tqbfHonestMessage {n : ℕ}
    (st : TQBFStatement 𝔽 n) (i : Fin n)
    (chs : Fin i.val → 𝔽) : CPoly.CMvPolynomial 1 𝔽 :=
  let matrixPoly : CPoly.CMvPolynomial n 𝔽 :=
    SharpSAT.arithmetize st.matrix
  have hn : (n - i.val) + i.val = n := by have := i.isLt; omega
  let substituted : CPoly.CMvPolynomial (n - i.val) 𝔽 :=
    CMvPolynomial.specializeFirst i.val chs (hn.symm ▸ matrixPoly)
  have hm : n - i.val = (n - i.val - 1) + 1 := by
    have := i.isLt; omega
  arithmetizeLeavingFirst
    (fun k : Fin (n - i.val - 1) =>
      st.quantifiers ⟨i.val + 1 + k.val,
        by have := i.isLt; have := k.isLt; omega⟩)
    (hm ▸ substituted)

/-- The honest prover for the Shamir TQBF protocol. -/
noncomputable def tqbfHonestProver [Fintype 𝔽] [DecidableEq 𝔽] {n : ℕ} :
    Prover (tqbfProtocol (𝔽 := 𝔽) (n := n)) where
  respond := fun st i chs => tqbfHonestMessage st i chs

end HonestProver

/-- **TQBF ∈ IP.** For each `n` and every sufficiently large finite field,
the language of valid QBFs of arity `n` admits an interactive proof. The
"sufficiently large" condition `3 · 2^n ≤ |𝔽|` bounds the total
Schwartz-Zippel soundness error by `1/3` across the `n` rounds. (Field
elements remain `O(n)` bits since `|𝔽|` is at most `2^{O(n)}`, so the
verifier stays polynomial-time — this is a classical IP-compatible bound.)

Not yet proved — see the file header for the remaining pieces. -/
theorem tqbf_inIP
    (𝔽 : Type) [Field 𝔽] [Fintype 𝔽] [BEq 𝔽] [LawfulBEq 𝔽] [DecidableEq 𝔽]
    (n : ℕ)
    (_hfield : 3 * 2 ^ n ≤ Fintype.card 𝔽) :
    InIP (fun Q : QBF n => Q.Valid) := by
  sorry

end TQBF
