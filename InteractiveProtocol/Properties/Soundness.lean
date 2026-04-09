import InteractiveProtocol.Properties.Probability

/-! ## Soundness and Completeness -/

/-- A public-coin interactive protocol has **soundness error** `ε` with respect to
    a validity predicate `isTrue` if: for every cheating prover `P` and every
    false statement `st`, the probability the verifier accepts is at most `ε`.

    This is the key property that the Fiat-Shamir transformation preserves
    (in the Random Oracle Model). -/
def hasSoundnessError {S C : Type*} {n : ℕ} [Fintype C]
    (ip : PublicCoinProtocol S C n)
    (isTrue : S → Prop) (ε : S → ℚ) : Prop :=
  ∀ (st : S) (P : Prover ip),
    ¬ isTrue st →
    probAccept ip st P ≤ ε st

/-- A public-coin interactive protocol has **perfect completeness** with respect to
    a validity predicate `isTrue` and an honest prover if:
    for every true statement, the verifier always accepts. -/
def hasPerfectCompleteness {S C : Type*} {n : ℕ} [Fintype C]
    (ip : PublicCoinProtocol S C n)
    (isTrue : S → Prop) (honest : Prover ip) : Prop :=
  ∀ (st : S),
    isTrue st →
    probAccept ip st honest = 1

/-- A weaker version: **statistical completeness** with completeness error `δ`.
    For every true statement, the honest prover is accepted with probability ≥ 1 - δ. -/
def hasCompletenessError {S C : Type*} {n : ℕ} [Fintype C]
    (ip : PublicCoinProtocol S C n)
    (isTrue : S → Prop) (honest : Prover ip) (δ : ℚ) : Prop :=
  ∀ (st : S),
    isTrue st →
    probAccept ip st honest ≥ 1 - δ
